import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothLocal.Analytic

variable {ι α : Type*} [DecidableEq ι]

theorem finite_product_one_factor_bound (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (x : α)
    (hb : ∀ i ∈ s.erase j, ‖f i x‖ ≤ B) :
    ‖∏ i ∈ s, f i x‖ ≤ B ^ (s.erase j).card * ‖f j x‖ := by
  have hprod : ‖∏ i ∈ s.erase j, f i x‖ ≤ B ^ (s.erase j).card := by
    calc
      _ ≤ ∏ i ∈ s.erase j, ‖f i x‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _i ∈ s.erase j, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hb
      _ = _ := Finset.prod_const B
  rw [← Finset.prod_erase_mul s (fun i => f i x) hj, norm_mul]
  exact mul_le_mul hprod le_rfl (norm_nonneg _) (pow_nonneg hB _)

variable [MeasurableSpace α] {μ : Measure α} {U : Set α}

theorem finite_product_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s.erase j, ∀ x ∈ U, ‖f i x‖ ≤ B) :
    eLpNorm' (fun x => ∏ i ∈ s, f i x) (2 : ℝ) (μ.restrict U) ≤
      ‖B ^ (s.erase j).card‖ₑ * eLpNorm' (f j) (2 : ℝ) (μ.restrict U) := by
  have hdom : ∀ᵐ x ∂(μ.restrict U),
      ‖∏ i ∈ s, f i x‖ ≤ ‖B ^ (s.erase j).card * f j x‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hB (s.erase j).card)]
    exact finite_product_one_factor_bound s f hj hB x (fun i hi => hb i hi x hx)
  calc
    _ ≤ eLpNorm' (fun x => B ^ (s.erase j).card * f j x) (2 : ℝ) (μ.restrict U) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f j)
      (B ^ (s.erase j).card) (by norm_num)

theorem finite_product_eLpNorm_two_of_aestronglyMeasurable
    (indices : Finset ι) (factors : ι → α → ℝ) {chosen : ι} (hchosen : chosen ∈ indices)
    {bound : ℝ} (hbound : 0 ≤ bound) (hU : MeasurableSet U)
    (hb : ∀ index ∈ indices.erase chosen, ∀ point ∈ U, ‖factors index point‖ ≤ bound)
    (hmeas : AEStronglyMeasurable
      (fun point => ∏ index ∈ indices, factors index point) (μ.restrict U)) :
    eLpNorm (fun point => ∏ index ∈ indices, factors index point) 2 (μ.restrict U) ≤
      ‖bound ^ (indices.erase chosen).card‖ₑ * eLpNorm (factors chosen) 2 (μ.restrict U) := by
  have hfactor : eLpNorm' (factors chosen) (2 : ℝ) (μ.restrict U) ≤
      eLpNorm (factors chosen) 2 (μ.restrict U) := by
    by_cases hfactorMeas : AEStronglyMeasurable (factors chosen) (μ.restrict U)
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hfactorMeas]
      norm_num
    · rw [eLpNorm_of_not_aestronglyMeasurable hfactorMeas]
      exact le_top
  calc
    _ = eLpNorm' (fun point => ∏ index ∈ indices, factors index point)
        (2 : ℝ) (μ.restrict U) := by
      simpa only [ENNReal.toReal_ofNat] using
        (eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hmeas)
    _ ≤ ‖bound ^ (indices.erase chosen).card‖ₑ *
        eLpNorm' (factors chosen) (2 : ℝ) (μ.restrict U) :=
      finite_product_eLpNorm_two indices factors hchosen hbound hU hb
    _ ≤ _ := mul_le_mul_right hfactor _

theorem finite_product_memLp_two (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s.erase j, ∀ x ∈ U, ‖f i x‖ ≤ B)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (f i) (μ.restrict U))
    (hf : MemLp (f j) 2 (μ.restrict U)) :
    MemLp (fun x => ∏ i ∈ s, f i x) 2 (μ.restrict U) := by
  apply (hf.const_mul (B ^ (s.erase j).card)).of_le
    (s.aestronglyMeasurable_fun_prod hm)
  filter_upwards [ae_restrict_mem hU] with point hpoint
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hB (s.erase j).card)]
  exact finite_product_one_factor_bound s f hj hB point
    (fun index hindex => hb index hindex point hpoint)

end SmoothLocal.Analytic

end

end OAI
