import OAI.Combinatorics.BalancedRyser.Results

namespace OAI

universe u v w

example : Balanced.SelectionStatement.{u,v,w} := Balanced.selection
example : Balanced.SelectionStatement.{0,1,2} := Balanced.selection
example : Balanced.SelectionStatement.{2,0,1} := Balanced.selection

end OAI
