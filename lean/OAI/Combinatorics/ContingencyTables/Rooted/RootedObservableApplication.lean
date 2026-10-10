import OAI.Combinatorics.ContingencyTables.Rooted.RootedFactorialApplication
import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservableApplication

namespace OAI

/-! # Observable bounds from the actual selected-root factorial signatures -/

namespace ContingencyTables.RootedObservableApplication

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates
open ComplementChain ObservableBounds

variable {I J : Type*} [Fintype I] [Fintype J]

theorem transversal_variance (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (ha : 0≤alpha)
    (H : Set (Labels A×Bool) → ℝ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r, 0<w p r)
    (hgood : ∀ p∈pairs, ∀ r∈pairs, p≠r →
      slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅/(4*slotDefect pairs (RootedFactorialApplication.f A R alpha) ∅ p r)≤w p r) :
    slotVariance pairs (RootedFactorialApplication.f A R alpha) H ∅≤
      (Fintype.card (Labels A):ℝ)*(1+8*(Fintype.card (Labels A):ℝ)*(A.W:ℝ)^4)*
        restrictedEnergy (chainEdges pairs) (chainConductance pairs w (RootedFactorialApplication.f A R alpha)) H ∅ ∅ := by
  have hf := RootedFactorialApplication.first_properties A R alpha ha
  have hg := RootedFactorialApplication.second_properties A R alpha ha
  have ht := omission_twoLift_transversal_variance pairs (RootedFactorialApplication.f A R alpha) (RootedFactorialApplication.g A R alpha) H w
    ((A.W:ℝ)^2) (sq_nonneg _)
    (by simpa only [PairedLabels.length] using hf.1)
    (by simpa only [PairedLabels.length] using hg.1)
    (by simpa only [PairedLabels.length] using hf.2)
    (by simpa only [PairedLabels.length] using hg.2)
    PairedLabels.fresh PairedLabels.cover hw hgood
    (by
      intro S hS
      exact (plain_lifts_agree (labelCell A) (RootedCountIdentification.h A R alpha) S hS).symm)
    (by
      intro S hS
      apply firstLift_le_square_secondLift (labelCell A) (RootedCountIdentification.h A R alpha) S hS A.W
        (by have hW := A.hW; omega)
      · intro s
        rw [label_width]
        exact A.hsmall _ _ s.property
      · exact (RootedCountIdentification.h_positive A R alpha _).le)
  simpa only [PairedLabels.length,← pow_mul] using ht

theorem observable_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (ha : 0≤alpha)
    (hp : 0<Fintype.card (Labels A)) (H : Set (Labels A×Bool) → ℝ)
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r, 0<w p r)
    (hlower : ∀ p∈pairs, ∀ r∈pairs, p≠r →
      slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅/(4*slotDefect pairs (RootedFactorialApplication.f A R alpha) ∅ p r)≤w p r)
    (hupper : ∀ p∈pairs, ∀ r∈pairs, p≠r →
      w p r≤4*slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅/slotDefect pairs (RootedFactorialApplication.f A R alpha) ∅ p r) :
    chainVariance pairs w (RootedFactorialApplication.f A R alpha) (observableProjection pairs (RootedFactorialApplication.f A R alpha) H)≤
      observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)*
        chainDirichlet pairs w (RootedFactorialApplication.f A R alpha) H := by
  have hf := RootedFactorialApplication.first_properties A R alpha ha
  have hq : (1:ℝ)≤(A.W:ℝ)^2 := by
    have hW : (2:ℝ)≤A.W := by exact_mod_cast A.hW
    nlinarith
  have hne : (pairs : List ((Labels A×Bool)×(Labels A×Bool)))≠[] := by
    apply List.ne_nil_of_length_pos
    simpa only [PairedLabels.length] using hp
  have ht := omission_observable_poincare pairs PairedLabels.fresh hne PairedLabels.cover w hw
    (RootedFactorialApplication.f A R alpha) H (by simpa only [PairedLabels.length] using hf.1)
    (by simpa only [PairedLabels.length] using hf.2) ((A.W:ℝ)^2) hq hlower hupper
  simpa only [PairedLabels.length] using ht

end ContingencyTables.RootedObservableApplication

end OAI
