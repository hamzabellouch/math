import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Excluding rows with excessive original pair or triple cost -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]

 theorem bad_row_incidence (ξ : Measure A) (ν : Measure Z) [SFinite ξ] [SFinite ν]
    (F : A × Z → ℝ≥0∞) (B : A → ℝ≥0∞) (hB : Measurable B)
    (S : Set Z) (hS : MeasurableSet S) (M t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞)
    (hbound : ∀ p, F p ≤ M) (hsupport : ∀ p, p.2 ∉ S → F p = 0) :
    (∫⁻ p in {p : A × Z | t ≤ B p.1}, F p ∂ξ.prod ν) ≤
      (M*ν S)*((∫⁻ a, B a ∂ξ)/t) := by
  let D : Set A := {a | t ≤ B a}
  have hD : MeasurableSet D := measurableSet_le measurable_const hB
  have hp : {p : A × Z | t ≤ B p.1} = D ×ˢ univ := by ext p; simp [D]
  rw [hp,← Measure.prod_restrict]
  have hpoint : ∀ p, F p ≤ M*S.indicator (fun _ => (1:ℝ≥0∞)) p.2 := by
    intro p
    by_cases hz : p.2 ∈ S
    · simpa only [indicator_of_mem hz,mul_one] using hbound p
    · rw [hsupport p hz,indicator_of_notMem hz,mul_zero]
  calc
    _ ≤ ∫⁻ p, M*S.indicator (fun _ => (1:ℝ≥0∞)) p.2
        ∂(ξ.restrict D).prod (ν.restrict univ) := lintegral_mono hpoint
    _ = (M*ν S)*ξ D := by
      rw [Measure.restrict_univ,lintegral_prod _ (by fun_prop)]
      simp only [lintegral_const_mul M (measurable_const.indicator hS),
        lintegral_indicator_const hS,one_mul,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := mul_le_mul' le_rfl (meas_ge_le_lintegral_div hB.aemeasurable ht htop)

end Falconer

end OAI
