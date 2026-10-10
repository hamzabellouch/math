import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.EventWeight

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma relationMass_crossed (p : Law (α×β)) (q : Law (γ×δ)) (R : α→δ→Prop) :
    relationMass R (first p) (second q)=
      eventWeight (product p q) (fun z=>R z.1.1 z.2.2) := by
  rw [SharpRamseyFive.LowConflict.crossed_endpoint]
  unfold relationMass
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

end SharpRamseyFive.FiniteEntropy

end OAI
