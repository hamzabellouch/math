import OAI.Combinatorics.BalancedRyser.Incidence.SmallProjectiveStability

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem primeStability_proof : PrimeStability.{u} := by
  apply primeStability_of_smallProjective
  intro F field finite dec hprime hq B hB hsmall
  have hdec : dec = Classical.decEq F := Subsingleton.elim _ _
  cases hdec
  exact small_projective_stability hprime hq B hB hsmall

end Balanced

end OAI
