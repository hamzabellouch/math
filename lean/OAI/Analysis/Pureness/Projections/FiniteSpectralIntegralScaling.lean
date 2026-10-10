import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegral

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set
open scoped ENNReal NNReal

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem positive_cut_smul (r : ℝ≥0) (hr : 0 < r) (ε : ℝ≥0) (M : Positive D) :
    Positive.cut ε (Positive.smul r M) = Positive.smul r (Positive.cut (ε/r) M) := by
  apply Subtype.ext
  change cfcₙ (fun t : ℝ => max (t-ε) 0) ((r : ℝ) • M.1) =
    (r : ℝ) • cfcₙ (fun t : ℝ => max (t-(ε/r : ℝ≥0)) 0) M.1
  rw [← cfcₙ_comp_smul (r : ℝ) (fun t : ℝ => max (t-ε) 0) M.1,
    ← cfcₙ_smul (r : ℝ) (fun t : ℝ => max (t-(ε/r : ℝ≥0)) 0) M.1 (h0 := by simp only [zero_sub]; exact max_eq_right (neg_nonpos.mpr (NNReal.coe_nonneg _)))]
  apply cfcₙ_congr
  intro t ht
  change max ((r : ℝ)*t-ε) 0 = (r : ℝ)*max (t-(ε/r : ℝ≥0)) 0
  rw [NNReal.coe_div, mul_max_of_nonneg _ _ (show (0 : ℝ) ≤ r from r.2),mul_zero,mul_sub]
  congr 1
  field_simp

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finitePositiveClass_smul (n : ℕ) (M : Positive (FinMatrix A n))
    (r : ℝ≥0) (hr : 0 < r) :
    finitePositiveClass n (Positive.smul r M) = finitePositiveClass n M := by
  have h := positive_smul_cuntz_equiv M.1 r hr
  exact le_antisymm ((finitePositiveClass_le_iff n _ _).mpr h.1)
    ((finitePositiveClass_le_iff n _ _).mpr h.2)

lemma finiteDimensionDistribution_smul
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (M : Positive (FinMatrix A n)) (r : ℝ≥0) (hr : 0 < r) (t : ℝ) :
    finiteDimensionDistribution d n (Positive.smul r M) t =
      finiteDimensionDistribution d n M (t/r) := by
  unfold finiteDimensionDistribution
  rw [positive_cut_smul r hr,finitePositiveClass_smul n _ r hr]
  congr 3
  exact by
    by_cases ht : 0 ≤ t
    · simp [Real.toNNReal_div ht, Real.toNNReal_coe]
    · have htn : t ≤ 0 := (lt_of_not_ge ht).le
      rw [Real.toNNReal_eq_zero.mpr htn, zero_div]
      exact (Real.toNNReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg htn r.2)).symm

lemma positive_halfline_integral_div (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (r : ℝ) (hr : 0 < r) :
    (∫⁻ t in Ioi (0 : ℝ), f (t/r)) = ENNReal.ofReal r * ∫⁻ t in Ioi (0 : ℝ), f t := by
  let g := (Ioi (0 : ℝ)).indicator f
  have hg : Measurable g := hf.indicator measurableSet_Ioi
  have heq : (Ioi (0 : ℝ)).indicator (fun t => f (t/r)) = fun t => g (r⁻¹*t) := by
    funext t
    by_cases ht : 0 < t
    · simp [g,ht,inv_mul_eq_div,div_pos ht hr]
    · have hn : ¬ 0 < t/r := by simpa only [div_pos_iff_of_pos_right hr] using ht
      simp [g,ht,inv_mul_eq_div,hn]
  rw [← lintegral_indicator measurableSet_Ioi, heq, ← lintegral_map hg (show Measurable (fun t : ℝ => r⁻¹*t) from measurable_const.mul measurable_id),
    Real.map_volume_mul_left (inv_ne_zero hr.ne'), lintegral_smul_measure]
  simp only [inv_inv, abs_of_pos hr, smul_eq_mul]
  rw [lintegral_indicator measurableSet_Ioi]

theorem finiteSpectralIntegral_smul
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (r : ℝ≥0) :
    finiteSpectralIntegral d n (Positive.smul r M) = (r : ℝ≥0∞)*finiteSpectralIntegral d n M := by
  by_cases hr : r = 0
  · subst r
    have hzero : Positive.smul 0 M = Positive.zero := by apply Subtype.ext; change (0 : ℝ) • M.1 = 0; exact zero_smul ℝ M.1
    simp [hzero,finiteSpectralIntegral_zero]
  · have hrpos : 0 < r := pos_iff_ne_zero.mpr hr
    simp only [finiteSpectralIntegral,finiteDimensionDistribution_smul d n M r hrpos]
    rw [positive_halfline_integral_div _ (finiteDimensionDistribution_measurable d hd n M) r hrpos,
      ENNReal.ofReal_coe_nnreal]
end CuntzPureness

end

end OAI
