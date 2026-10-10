import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

/-!
# Energy of bounded functions with finite-measure support

Comparison with a constant indicator gives square integrability and an explicit
energy bound in terms of the uniform bound and the measure of the support set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem bounded_support_memLp_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfm : Measurable f)
    (S : Set X) (hS : MeasurableSet S) (hfin : μ S < ∞)
    (M : ℝ) (hM : 0 ≤ M) (hfM : ∀ x, |f x| ≤ M) (hs : ∀ x, x ∉ S → f x = 0) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M ^ 2 * μ.real S := by
  let g : X → ℝ := S.indicator (fun _ => M)
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hg : MemLp g 2 μ := (memLp_indicator_iff_restrict hS).mpr (memLp_const M)
  have hpoint (x : X) : |f x| ≤ |g x| := by
    by_cases hx : x ∈ S
    · simpa only [g, indicator_of_mem hx, abs_of_nonneg hM] using! hfM x
    · simp only [hs x hx, g, indicator_of_notMem hx, abs_zero, le_refl]
  have hf : MemLp f 2 μ := hg.of_le hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hpoint x)
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, g x ^ 2 ∂μ := integral_mono hf.integrable_sq hg.integrable_sq (fun x => by
      have hb := mul_self_le_mul_self (abs_nonneg (f x)) (hpoint x)
      simpa only [← pow_two, sq_abs] using! hb)
    _ = M ^ 2 * μ.real S := by
      have heq : (fun x => g x ^ 2) = S.indicator (fun _ => M ^ 2) := by
        funext x
        by_cases hx : x ∈ S <;> simp [g, hx]
      rw [heq, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]

theorem bounded_ball_support_energy {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hfm : Measurable f) (a : Ambient d) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hfM : ∀ x, |f x| ≤ M)
    (hs : ∀ x, r ≤ dist x a → f x = 0) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M ^ 2 * (G * r ^ n) := by
  have hm := hg.2 a r hr
  have hfin := lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  have hf := bounded_support_memLp_energy μ f hfm (ball a r) measurableSet_ball hfin M hM hfM
    (fun x hx => hs x (le_of_not_gt hx))
  refine ⟨hf.1, hf.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
  exact ENNReal.toReal_le_of_le_ofReal (by positivity [hg.1]) hm

end

end RieszRectifiability

end OAI
