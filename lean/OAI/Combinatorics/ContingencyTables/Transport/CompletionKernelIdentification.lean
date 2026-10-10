import OAI.Combinatorics.ContingencyTables.Transport.CompletionProposalLaw

namespace OAI

/-! # Identifying a complete transition law from its off-diagonal probabilities -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Normalization determines the remaining holding probability. -/
theorem law_ext_except (p q : RationalLaw X) (x : X)
    (h : ∀ y,y≠x → p.mass y=q.mass y) : p=q := by
  apply RationalLaw.ext
  funext y
  by_cases hy : y=x
  · subst y
    have hs : (∑ y,(p.mass y-q.mass y))=p.mass x-q.mass x := by
      apply Finset.sum_eq_single x
      · intro y _ hy
        rw [h y hy,sub_self]
      · simp
    rw [Finset.sum_sub_distrib,p.total,q.total,sub_self] at hs
    linarith
  · exact h y hy

end ContingencyTables.FirstSuccess

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]
variable (R : X → Option I → ℕ) (P : X → Option J → ℕ)
variable [∀ x,Nonempty (Table (R x) (P x))]

omit [∀ x,Nonempty (Table (R x) (P x))] in
/-- Only the proposal distribution at the current state is observed. -/
lemma completionStepLaw_proposal_at (p q : X → RationalLaw (Option X))
    (draw : (z : X) → RationalLaw (Table (R z) (P z))) (x : X) (h : p x=q x) :
    completionStepLaw R P p draw x=completionStepLaw R P q draw x := by
  unfold completionStepLaw
  rw [h]

/-- This identifies the actual draw-and-test transition, including holds;
no independent reversibility or stationarity assertion is imposed on it. -/
theorem uniformCompletionStep_eq (w : X → ℚ) (hw : ∀ y,0 ≤ w y)
    (htotal : ∑ y,w y ≤ 1) (x : X) (K : RationalLaw X)
    (hK : ∀ y,y≠x → K.mass y=w y*(acceptedCount R P x y:ℚ)/(blockCount R P x:ℚ)) :
    completionStepLaw R P (fun _ => proposalLaw w hw htotal)
      (fun z => uniformLaw (α := Table (R z) (P z))) x=K := by
  apply law_ext_except _ _ x
  intro y hy
  rw [completionStepLaw_mass_ne R P w hw htotal _ x y hy.symm,uniformAcceptedMass,hK y hy]
  ring

end
end ContingencyTables.CompletionTranslation

end OAI
