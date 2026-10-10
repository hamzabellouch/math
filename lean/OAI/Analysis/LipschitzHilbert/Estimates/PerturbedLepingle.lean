import OAI.Analysis.LipschitzHilbert.Estimates.ComplexVariation
import OAI.Analysis.LipschitzHilbert.Estimates.VariationPerturbation
import OAI.Analysis.LipschitzHilbert.Estimates.VariationMeasurable

namespace OAI

/-! Lépingle plus the actual square-summable smooth/dyadic error. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem lintegral_finiteCubicVariation_comparison {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (P M : ℕ → Ω → E)
    (hP : ∀ n, Measurable (P n)) (hM : ∀ n, Measurable (M n)) (N : ℕ) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) ∂μ) +
        8 * ∑ k : Fin (N + 1), ∫⁻ x, ‖P k x - M k x‖ₑ ^ 2 ∂μ := by
  have hpoint (x : Ω) :
      ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ≤
        2 * ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) +
          8 * ∑ k : Fin (N + 1), ‖P k x - M k x‖ₑ ^ 2 := by
    have h := ENNReal.ofReal_le_ofReal
      (finiteCubicVariation_comparison (fun n => P n x) (fun n => M n x) N)
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _)) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)] at h
    simpa only [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 2 / 3), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
  calc
    _ ≤ ∫⁻ x, 2 * ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) +
        8 * ∑ k : Fin (N + 1), ‖P k x - M k x‖ₑ ^ 2 ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left]
      · rw [lintegral_const_mul, lintegral_const_mul, lintegral_finsetSum]
        · intro k _
          exact ((hP _).sub (hM _)).enorm.pow_const _
        · exact Finset.measurable_sum _ fun k _ => ((hP _).sub (hM _)).enorm.pow_const _
        · exact (measurable_finiteCubicVariation M hM N).ennreal_ofReal.pow_const _
      · exact measurable_const.mul
          ((measurable_finiteCubicVariation M hM N).ennreal_ofReal.pow_const _)

theorem measurable_complex_martingale {Ω κ : Type*} [m : MeasurableSpace Ω] [Fintype κ]
    {μ : Measure Ω} {ℱ : Filtration ℕ m} {M : ℕ → Ω → EuclideanSpace ℂ κ}
    (hRe : ∀ k, Martingale (fun n x => (M n x k).re) ℱ μ)
    (hIm : ∀ k, Martingale (fun n x => (M n x k).im) ℱ μ) (n : ℕ) :
    Measurable (M n) := by
  have hre (k : κ) : Measurable (fun x => (M n x k).re) :=
    ((hRe k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have him (k : κ) : Measurable (fun x => (M n x k).im) :=
    ((hIm k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hc (k : κ) : Measurable (fun x => M n x k) := by
    have h := (Complex.continuous_ofReal.measurable.comp (hre k)).add
      ((Complex.continuous_ofReal.measurable.comp (him k)).mul_const Complex.I)
    change Measurable (fun x => ((M n x k).re : ℂ) + (M n x k).im * Complex.I) at h
    simpa only [Complex.re_add_im] using h
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hc)

/-- Only the scalar published input is assumed. The error term is the
sum of the actual squared smooth/dyadic differences. -/
theorem lepingle_complex_comparison (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (P M : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ n, Measurable (P n)) →
          (∀ k, Martingale (fun n x => (M n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (M n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (M n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (M n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
              2 * (C : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖M N x‖ₑ ^ 2 ∂μ) +
                8 * ∑ k : Fin (N + 1), ∫⁻ x, ‖P k x - M k x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ P M hP hRe hIm hRe2 hIm2 N
  have h := lintegral_finiteCubicVariation_comparison μ P M hP
    (measurable_complex_martingale hRe hIm) N
  exact h.trans (add_le_add (by
    simpa only [mul_assoc] using
      mul_le_mul_right (hbound Ω m μ hμ κ ℱ M hRe hIm hRe2 hIm2 N) 2) le_rfl)

end LipschitzHilbert

end

end OAI
