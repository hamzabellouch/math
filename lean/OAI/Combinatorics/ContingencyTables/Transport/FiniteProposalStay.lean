import OAI.Combinatorics.ContingencyTables.Transport.CompletionProposalLaw

namespace OAI

/-! # A finite proposal with unused words held at the current state -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X : Type*} [Fintype X] [DecidableEq X]

def proposalStayLaw (w : X → ℚ) (hw : ∀ y,0 ≤ w y)
    (htotal : ∑ y,w y ≤ 1) (x : X) : RationalLaw X :=
  mapLaw (proposalLaw w hw htotal) (fun y => y.getD x)

lemma proposalStayLaw_mass (w : X → ℚ) (hw : ∀ y,0 ≤ w y)
    (htotal : ∑ y,w y ≤ 1) (x y : X) :
    (proposalStayLaw w hw htotal x).mass y=
      w y+if x=y then 1-∑ z,w z else 0 := by
  change (∑ z : Option X,if z.getD x=y then (proposalLaw w hw htotal).mass z else 0)=_
  rw [Fintype.sum_option]
  simp only [Option.getD_none,Option.getD_some,proposalLaw]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true]
  ring

end
end ContingencyTables.CompletionTranslation

end OAI
