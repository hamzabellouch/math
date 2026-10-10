import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoff

namespace OAI

namespace Ostmann.Arithmetic
open Set Filter
open scoped ContDiff Topology

theorem giantCell_mul_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ) (p : E → ℝ) (f : E → ℂ) (hp : ContDiff ℝ ∞ p)
    (hf : ∀ x, 0 < p x → ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => (giantCell G (p x) : ℂ) * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < p x
  · exact ((Complex.ofRealCLM.contDiff.comp ((giantCell_contDiff G).comp hp)).contDiffAt).mul (hf x hx)
  · have hlt : p x < Real.exp (G - 1) := (le_of_not_gt hx).trans_lt (Real.exp_pos _)
    apply (show ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) x from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hp.continuous.continuousAt.eventually (eventually_lt_nhds hlt)] with y hy
    simp only [giantCell_zero_of_le_lower G hy.le, Complex.ofReal_zero, zero_mul]

theorem giantCell_mul_contDiff_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ) (p : E → ℝ) (f : E → ℂ) (hp : ContDiff ℝ ∞ p)
    (hf : ∀ x, 0 < p x → ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ 1 (fun x => (giantCell G (p x) : ℂ) * f x) :=
  (giantCell_mul_contDiff G p f hp hf).of_le (by simp)

end Ostmann.Arithmetic

end OAI
