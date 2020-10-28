# look into math packages that can allow me to work with formulas somehow, instead of strings
# or lists of types


# 1. (DONE) Parse input to get constraints
# 2. (DONE) Replace each variable x with x' - x'', collect variable list
# 3. (DONE) Get slack variables/forms (this is the first output)
# 4. (DONE) Take constraint with most negative constant term and rewrite constraint in terms of x0
# 5. (DONE) Plug x0 into other constraints and goal term.
# 6. (DONE) Now, every constraint has positive constant term, so set all vars on right side of each constraint to 0 and and all left side vars equal to constant value in constraint
#	(this is the next output)
# 7. While maxValue < 0 pivot:
#		if there are no variables in term (first arg) with positive coeff, return UNSAT
#		choose a variable with positive coeff
#			find the constraint that restricts its increase the most
# 			rewrite constraint in terms of the variable
#			plug variable (represents constraint) into term and other constraints
#	print values of variables
from sympy import *
from collections import OrderedDict
import sys

var_to_value = OrderedDict()

def parse(inp):
	inp = inp.replace(" ", "")

	# skip "AND("
	inp = inp[4:]

	# replace ")" with "," to mark last constraint
	inp = inp[:-1] + ","

	constraints, variables = [], []
	while "," in inp:
		comma = inp.index(",")

		constraints.append(inp[:comma])

		idx = 0
		var = ""
		new_var = True
		while idx < comma:
			if inp[idx].isalpha() and new_var:
				var = inp[idx]
				new_var = False

			elif inp[idx].isalnum() and not new_var:
				var += inp[idx]

			else:
				new_var = True
				if var and var not in variables:
					variables.append(var)

			idx += 1

		inp = inp[comma+1:]

	return constraints, variables


assert parse("AND(x + 1/2*y - 3*z0 >= 1, 2 * x - 1/2 * z0 <= 1)") == \
(['x+1/2*y-3*z0>=1', '2*x-1/2*z0<=1'], ['x', 'y', 'z0'])


def symp(constraints, variables):
	eqs = sympify(constraints)


	syms = OrderedDict()
	for var in variables:
		syms[var] = symbols(var)

	nonneg_syms = OrderedDict()
	for var, sym in syms.items():
		nonneg_syms[var] = sym
		nonneg_syms[var + 'prime'] = symbols(var + 'prime')

	syms = nonneg_syms

	new_eqs = []
	for eq in eqs:
		for var, sym in syms.items():
			if not var.endswith('prime'):
				eq = eq.subs(syms[var], syms[var] - syms[var + 'prime'])

		new_eqs.append(eq)

	eqs = new_eqs
	return eqs, syms


# 1. replaces original eq
# 2. Add slack var to variable dict
def slackify(eqs, syms):
	slack_eqs = [None] * len(eqs)

	# add x0
	syms['x0'] = symbols('x0')

	for i, eq in enumerate(eqs):
		slack_var = 'slack' + str(i+1)
		syms[slack_var] = symbols(slack_var)

		arg1, arg2 = eq.args
		if eq.__class__.__name__ == 'GreaterThan':
			slack_eqs[i] = Eq(syms[slack_var], arg1 - arg2 + syms['x0'])

		elif eq.__class__.__name__ == 'StrictGreaterThan':
			slack_eqs[i] = Eq(syms[slack_var], arg1 - arg2 + syms['x0'] - 1/1000000)
		
		elif eq.__class__.__name__ == 'LessThan':
			slack_eqs[i] = Eq(syms[slack_var], arg2 - arg1 + syms['x0'])
		 
		elif eq.__class__.__name__ == 'StrictLessThan':
			slack_eqs[i] = Eq(syms[slack_var], arg2 - arg1 + syms['x0'] - 1/1000000)
		else:
			raise NotImplementedError

	return slack_eqs, syms

# sl = slackify(*symp(*parse("AND(x >= 1, 2 * x <= 1)")))
# sl = slackify(*symp(*parse("AND(x >= 2, 2 * x <= 4)")))

# x = 0, y = 1
# sl = slackify(*symp(*parse("AND(x + y >= 1, 2 * x - y <= 0)")))

# x = 0, y = 1/2
# sl = slackify(*symp(*parse("AND ( x + 2 * y >= 1, 2 * x  + 1 <= 1, 2 * x + 2 * y <=1)")))

# UNSAT
# sl = slackify(*symp(*parse("AND (x  >= 1, 2 * x <= 1)")))

# UNSAT
# sl = slackify(*symp(*parse("AND (x + 2 * y >= 1, 2 * x + y >= 1, 2 * x + 2 * y <= 1)")))

# x = 1, y = 0
# sl = slackify(*symp(*parse("AND (x + 2 * y >= 1, 2* x + y  >=1, x + y <= 1)")))

# sl = slackify(*symp(*parse("AND (x  > 2)")))
# sl = slackify(*symp(*parse("AND (x  > 2, x < 3)")))
# sl = slackify(*symp(*parse("AND (x  > 2, x < 2)")))
# sl = slackify(*symp(*parse("AND (x+y<0)")))
# sl = slackify(*symp(*parse("AND (x+y-z<0)")))
# sl = slackify(*symp(*parse("AND (x+y>0, x+y<0)")))
# sl = slackify(*symp(*parse("AND (x+y>0, x+y-z<0)")))
# sl = slackify(*symp(*parse("AND (x+y+z+a>0, x+y-z<0)")))
# sl = slackify(*symp(*parse("AND (x+y+z+a>=0, x+y-z<=0)")))
# sl = slackify(*symp(*parse("AND (x+y+z-3>=0, x+y-z<=0)")))







# sl = slackify(*symp(*parse("AND(x <= 2)")))

sl = slackify(*symp(*parse("AND(x < 0)")))





def output_slack(eqs, syms):
	term = '-x0'
	formula = 'AND('
	for i in range(len(eqs)-1):
		formula += str(eqs[i]) + ', '

	formula += str(eqs[-1])
	formula += ')'

	currentOptimumVertex = [sym for sym in syms.keys()]

	maximalValue = 'v'

	return('OPT' + str((term, formula, currentOptimumVertex, maximalValue)))

print(output_slack(*sl))
print()


def get_constant(arg, syms):
	if isinstance(arg, int):
		return arg

	poly = Poly(arg, syms.values())

	if len(poly.free_symbols) == len(poly.coeffs()):
		return 0

	return arg.func(*[term for term in arg.args if not term.free_symbols])

# x,y,z,x0 = symbols('x,y,z,x0')

# syms = {'x': x, 'y': y, 'z': z, 'x0': x0}
# print(get_constant(-3,syms))
# print(get_constant(x-3,syms))
# print(get_constant(x,syms))
# print(get_constant(-x,syms))
# print(get_constant(-x-z,syms))

def print_early_solution(syms):
	out = ''
	for sym in syms.keys():
		if sym != 'x0' and not sym.startswith('slack')\
		 and not sym.endswith('prime'):
			out += sym
			out += '=0,'

	return out[:-1]


assert print_early_solution({'x': 'x', 'xprime': 'xprime', 'y': 'y',\
 'yprime': 'yprime', 'z0': 'z0', 'z0prime': 'z0prime', 'x0': 'x0',\
  'slack1': 'slack1', 'slack2': 'slack2'}) == 'x=0,y=0,z0=0'


def print_pivot_before_early_solution(slack_eqs, syms):
	term = '-x0'
	formula = 'AND('
	for i in range(len(slack_eqs)-1):
		formula += str(slack_eqs[i]) + ', '

	formula += str(slack_eqs[-1])
	formula += ')'

	for eq in slack_eqs:
		var = eq.args[0]
		if str(var) not in var_to_value:
			var_to_value[str(var)] = get_constant(eq.args[1], syms)

	for sym in syms.keys():
		if sym not in var_to_value:
			var_to_value[sym] = 0

	currentOptimumVertex = []
	for key in syms.keys():
		currentOptimumVertex.append(var_to_value[key])

	maximalValue = 0

	return('OPT' + str((term, formula, currentOptimumVertex, maximalValue)))


# rewrote constraint w most neg constant and plugged into goal and constraints
def find_most_neg_constant(slack_eqs, syms):
	constant = 0
	most_neg_eq_idx = 0

	for i, eq in enumerate(slack_eqs):
		eq_constant = get_constant(slack_eqs[i].args[1], syms)
		if eq_constant < constant:
			constant = eq_constant
			most_neg_eq_idx = i 

	if constant == 0:
		# solution already found, all vars should be 0
		print(print_pivot_before_early_solution(slack_eqs, syms))
		print()
		print(print_early_solution(syms))
		sys.exit(0)


	# rewrite eq in terms of x0
	x0 = solve(slack_eqs[most_neg_eq_idx], syms['x0'])[0]
	x0_eq = Eq(syms['x0'], x0)
	
	# plug x0 into constraints and goal term
	goal = -syms['x0']
	goal = goal.subs(syms['x0'], x0)
	
	sub_eqs = [None] * len(slack_eqs)
	for i, eq in enumerate(slack_eqs):
		if i != most_neg_eq_idx:
			sub_eqs[i] = eq.subs(syms['x0'], x0)
		else:
			sub_eqs[i] = Eq(syms['x0'], solve(eq, syms['x0'])[0])

	return sub_eqs, syms, goal


potential_end = find_most_neg_constant(*sl)

if isinstance(potential_end, str):
	print(potential_end)
	sys.exit(0)


def output_before_pivot(sub_eqs, syms, goal):
	term = goal
	formula = 'AND('
	for i in range(len(sub_eqs)-1):
		formula += str(sub_eqs[i]) + ', '

	formula += str(sub_eqs[-1])
	formula += ')'

	syms_on_left_side_of_constraints = []
	for eq in sub_eqs:
		var = eq.args[0]
		if var not in syms_on_left_side_of_constraints:
			syms_on_left_side_of_constraints.append(var)

	for eq in sub_eqs:
		var = eq.args[0]
		if str(var) not in var_to_value:
			var_to_value[str(var)] = get_constant(eq.args[1], syms)

	for sym in syms.keys():
		if sym not in var_to_value:
			var_to_value[sym] = 0

	currentOptimumVertex = []
	for key in syms.keys():
		currentOptimumVertex.append(var_to_value[key])

	return('OPT' + str((term, formula, currentOptimumVertex, -var_to_value['x0'])))

print(output_before_pivot(*find_most_neg_constant(*sl)))
print()

def output_pivot_step(sub_eqs, new_sub_eqs, syms, goal, maxValue, pivot_var):
	term = goal
	formula = 'AND('
	for i in range(len(new_sub_eqs)-1):
		formula += str(new_sub_eqs[i]) + ', '

	formula += str(new_sub_eqs[-1])
	formula += ')'

	pivotted_var, eq_to_pivot_idx, greatest_negative_ratio = pivot_var

	for key in var_to_value.keys():
		var_to_value[key] = 0

	for eq in new_sub_eqs:
		var = eq.args[0]
		var_to_value[str(var)] = get_constant(eq.args[1], syms)

	currentOptimumVertex = []
	for key in syms.keys():
		currentOptimumVertex.append(var_to_value[key])

	return('OPT' + str((term, formula, currentOptimumVertex, maxValue)))


def output_solution(sub_eqs, syms):
	out = ''
	added = []
	for eq in sub_eqs:
		var = str(eq.args[0])
		if not var.startswith('slack') and not var.endswith('prime')\
		 and var != 'x0':
		 	out += var
		 	out += '=' + str(get_constant(eq.args[1], syms)) + ','
		 	added.append(var)

	for sym in syms.keys():
		if sym != 'x0' and not sym.startswith('slack')\
		 and not sym.endswith('prime') and sym not in added:
			out += sym
			out += '=0,'

	return out[:-1]

def output_final_pivot(sub_eqs, syms, goal, maxValue):
	term = goal
	formula = 'AND('
	for i in range(len(sub_eqs)-1):
		formula += str(sub_eqs[i]) + ', '

	formula += str(sub_eqs[-1])
	formula += ')'

	added = []
	for eq in sub_eqs:
		var = str(eq.args[0])
		if not var.startswith('slack') and not var.endswith('prime')\
		 and var != 'x0':
			var_to_value[str(var)] = get_constant(eq.args[1], syms)
			added.append(var)

	for sym in syms.keys():
		if sym not in added:
			var_to_value[sym] = 0

	currentOptimumVertex = []
	for key in syms.keys():
		currentOptimumVertex.append(var_to_value[key])

	maximalValue = 0

	return('OPT' + str((term, formula, currentOptimumVertex, maximalValue)))


def pivot(sub_eqs, syms, goal, maxValue):
	while maxValue < 0:

		# check if goal has any symbols with positive coeff
		goal_poly = Poly(goal, syms.values())
		coeffs = None
		if get_constant(goal, syms) != 0:
			coeffs = goal_poly.coeffs()
			coeffs = coeffs[:-1]

		var_to_pivot_idx = -1
		var_to_pivot = None

		for i, sym in enumerate(syms.keys()):
			if goal.coeff(syms[sym]) > 0 and "prime" not in sym:
				var_to_pivot_idx = i
				var_to_pivot = sym
				break

		if var_to_pivot_idx == -1:
			print()
			print("UNSAT")
			return

		# find the eq that restricts var_to_pivot the most
		# find eq with greatest negative ratio of (constant/coeff of var_to_pivot)
		# negative because each neg coeff has corresponding pos coeff
		eq_to_pivot_idx = 0
		greatest_negative_ratio = float("-inf")
		for i, eq in enumerate(sub_eqs):
			coeff_pivot = eq.args[1].coeff(var_to_pivot)

			if coeff_pivot == 0:
				continue

			ratio = get_constant(eq.args[1], syms) / coeff_pivot
			if ratio > greatest_negative_ratio and not (get_constant(eq.args[1], syms) == 0 and coeff_pivot > 0):
				greatest_negative_ratio = ratio
				eq_to_pivot_idx = i

		# rewrite eq_to_pivot in terms of var_to_pivot
		# rewrite eq in terms of x0
		pivotted_var = solve(sub_eqs[eq_to_pivot_idx], syms[var_to_pivot])[0]
		pivotted_eq = Eq(syms[var_to_pivot], pivotted_var)

		# plug pivotted_var into goal and eqs
		goal = goal.subs(syms[var_to_pivot], pivotted_var)
	
		new_sub_eqs = [None] * len(sub_eqs)
		for i, eq in enumerate(sub_eqs):
			if i != eq_to_pivot_idx:
				new_sub_eqs[i] = eq.subs(syms[var_to_pivot], pivotted_var)
			else:
				new_sub_eqs[i] = Eq(syms[var_to_pivot],\
				 solve(eq, syms[var_to_pivot])[0])

		maxValue = get_constant(goal, syms)
		if maxValue < 0:
			print(output_pivot_step(sub_eqs, new_sub_eqs, syms, goal, maxValue,\
			 (syms[var_to_pivot], eq_to_pivot_idx, -greatest_negative_ratio)))

		sub_eqs = new_sub_eqs

	print(output_final_pivot(sub_eqs, syms, goal, maxValue))
	print()
	print(output_solution(sub_eqs, syms))
	return

pivot(*find_most_neg_constant(*sl), -var_to_value['x0'])



