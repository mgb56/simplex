import sys
import os
from simplex import *

if len(sys.argv) != 2 or sys.argv[0] != "output.py":
	sys.exit("Usage: python output.py <input_string>")

constraints, variables = parse(sys.argv[1])

eqs, syms = symp(constraints, variables)

slack_eqs, syms = slackify(eqs, syms)

print(output_slack(slack_eqs, syms))
print()

potential_end = find_most_neg_constant(slack_eqs, syms)
if isinstance(potential_end, str):
	print(potential_end)
	sys.exit(0)

print(output_before_pivot(*potential_end))
print()
pivot(*potential_end, -var_to_value['x0'])