import OAI.Geometry.RCD.Coordinates.NormalizedSubplanData

namespace OAI

/-! # Testing a half-restricted plan detects the absolute mean error

Adding half the original plan keeps the subplan mass at least one half.
Its normalization therefore increases compression by at most a factor two.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

def halfRestrictedMeasure (μ : Measure X) (S : Set X) : Measure X :=
  (1/2:ℝ≥0∞) • (μ+μ.restrict S)

theorem halfRestrictedMeasure_le (μ : Measure X) (S : Set X) :
    halfRestrictedMeasure μ S ≤ μ := by
  intro T
  simp only [halfRestrictedMeasure,Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  calc
    _ ≤ (1/2:ℝ≥0∞)*(μ T+μ T) := mul_le_mul' le_rfl
      (add_le_add le_rfl (show μ.restrict S T ≤ μ T from Measure.restrict_le_self T))
    _ = μ T := by
      have hh : (2:ℝ≥0∞)⁻¹+(2:ℝ≥0∞)⁻¹=1 := by
        rw [← two_mul,ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      rw [mul_add,← add_mul]
      simp only [one_div,hh,one_mul]

theorem halfRestrictedMeasure_mass_lower (μ : Measure X) [IsProbabilityMeasure μ] (S : Set X) :
    (1/2:ℝ≥0∞) ≤ halfRestrictedMeasure μ S univ := by
  simp only [halfRestrictedMeasure,Measure.smul_apply,Measure.add_apply,smul_eq_mul,measure_univ]
  simpa only [mul_one] using mul_le_mul' (le_refl (1/2:ℝ≥0∞))
    (le_add_right le_rfl : (1:ℝ≥0∞) ≤ 1+μ.restrict S univ)

theorem halfRestrictedMeasure_mass_ne_zero (μ : Measure X) [IsProbabilityMeasure μ] (S : Set X) :
    halfRestrictedMeasure μ S univ ≠ 0 :=
  ne_of_gt ((by norm_num : (0:ℝ≥0∞)<1/2).trans_le (halfRestrictedMeasure_mass_lower μ S))

theorem submeasure_integral_tendsto_zero
    (μ κ : ℕ → Measure X) [∀ k, IsProbabilityMeasure (μ k)]
    (hle : ∀ k, κ k ≤ μ k) (hzero : ∀ k, κ k univ ≠ 0) (f : ℕ → X → ℝ)
    (hlim : Tendsto (fun k => ∫ x, f k x ∂((κ k univ)⁻¹ • κ k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x ∂κ k) atTop (𝓝 0) := by
  have hfinite (k : ℕ) : κ k univ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (μ k) univ) (hle k univ)
  have heq (k : ℕ) : (∫ x, f k x ∂κ k)=
      (κ k).real univ*(∫ x, f k x ∂((κ k univ)⁻¹ • κ k)) := by
    rw [integral_smul_measure,smul_eq_mul,ENNReal.toReal_inv]
    change _=(κ k univ).toReal*((κ k univ).toReal⁻¹*_)
    rw [← mul_assoc,mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hzero k,hfinite k⟩),one_mul]
  apply squeeze_zero_norm _ (by simpa only [norm_zero] using hlim.norm)
  intro k
  rw [heq,norm_mul,Real.norm_of_nonneg measureReal_nonneg]
  have hm : (κ k).real univ ≤ 1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      ENNReal.toReal_mono (measure_ne_top (μ k) univ) (hle k univ)
  exact mul_le_of_le_one_left (norm_nonneg _) hm

theorem halfRestrictedMeasure_abs_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hm : Measurable f) (hi : Integrable f μ) :
    (∫ x, |f x| ∂μ)=4*(∫ x, f x ∂halfRestrictedMeasure μ {x | 0 ≤ f x})-
      3*(∫ x, f x ∂μ) := by
  let S := {x | 0 ≤ f x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hm
  have hI : Integrable (S.indicator f) μ := hi.indicator hS
  have habs : (∫ x, |f x| ∂μ)=2*(∫ x in S, f x ∂μ)-(∫ x, f x ∂μ) := by
    calc
      _ = ∫ x, 2*S.indicator f x-f x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |f x|=2*S.indicator f x-f x
          by_cases hx : 0 ≤ f x
          · rw [Set.indicator_of_mem (show x∈S from hx),abs_of_nonneg hx]
            ring
          · have hx' : f x < 0 := lt_of_not_ge hx
            rw [Set.indicator_of_notMem (show x∉S from hx),abs_of_neg hx',mul_zero,zero_sub]
      _ = _ := by
        rw [integral_sub (hI.const_mul 2) hi,integral_const_mul,integral_indicator hS]
  have hk : (∫ x, f x ∂halfRestrictedMeasure μ S)=
      (1/2:ℝ)*((∫ x, f x ∂μ)+(∫ x in S, f x ∂μ)) := by
    rw [halfRestrictedMeasure,integral_smul_measure,integral_add_measure hi hi.restrict,smul_eq_mul]
    norm_num
  change _=4*(∫ x, f x ∂halfRestrictedMeasure μ S)-3*(∫ x, f x ∂μ)
  rw [hk,habs]
  ring

theorem integral_abs_tendsto_of_halfRestrictedMeans
    (μ : ℕ → Measure X) [∀ k, IsProbabilityMeasure (μ k)]
    (f : ℕ → X → ℝ) (hm : ∀ k, Measurable (f k)) (hi : ∀ k, Integrable (f k) (μ k))
    (hmean : Tendsto (fun k => ∫ x, f k x ∂μ k) atTop (𝓝 0))
    (hhalf : Tendsto (fun k =>
      ∫ x, f k x ∂((halfRestrictedMeasure (μ k) {x | 0 ≤ f k x} univ)⁻¹ •
        halfRestrictedMeasure (μ k) {x | 0 ≤ f k x})) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |f k x| ∂μ k) atTop (𝓝 0) := by
  have hκ := submeasure_integral_tendsto_zero μ
    (fun k => halfRestrictedMeasure (μ k) {x | 0 ≤ f k x})
    (fun k => halfRestrictedMeasure_le _ _) (fun k => halfRestrictedMeasure_mass_ne_zero _ _) f hhalf
  have hh := (hκ.const_mul 4).sub (hmean.const_mul 3)
  simpa only [halfRestrictedMeasure_abs_integral _ _ (hm _) (hi _),mul_zero,sub_zero] using hh

end RegularPointCoordinates

end

end OAI
