import OAI.MeasureTheory.Falconer.Radial.RegularizationRadialGain
import OAI.MeasureTheory.Falconer.Recursion.IntermediateProfiles

namespace OAI

/-! # Source regularization preserves almost-everywhere bounds for the original reverse laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem sourceClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : sourceClass Q μ N B p ≪ μ := by
  unfold sourceClass
  rw [normalized_regularization_class_eq_cond]
  exact ProbabilityTheory.cond_absolutelyContinuous

theorem sourceClass_conditional_absolutelyContinuous (Q : DyadicCube d)
    (μ : Measure (Space d)) (N B : ℕ) (p P : CellPath d) :
    ProbabilityTheory.cond (sourceClass Q μ N B p) (Q.descendant P).carrier ≪ μ :=
  ProbabilityTheory.cond_absolutelyContinuous.trans (sourceClass_absolutelyContinuous Q μ N B p)

theorem sourceClass_original_ae (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) {P : Space d → Prop} (hP : ∀ᵐ z ∂μ, P z) :
    ∀ᵐ z ∂sourceClass Q μ N B p, P z :=
  (sourceClass_absolutelyContinuous Q μ N B p).ae_le hP

theorem sourceClass_conditional_original_ae (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p P : CellPath d) {R : Space d → Prop} (hR : ∀ᵐ z ∂μ, R z) :
    ∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p) (Q.descendant P).carrier, R z :=
  (sourceClass_conditional_absolutelyContinuous Q μ N B p P).ae_le hR

end Falconer.Regularization

end OAI
