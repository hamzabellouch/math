import OAI.Analysis.CircleDomains.Probability.CompactMeasureMajorantCost
import OAI.Analysis.CircleDomains.Modulus.CompactMajorantSeparation
import OAI.Analysis.CircleDomains.Probability.ContinuousMeasureModulus
import OAI.Analysis.CircleDomains.Probability.CompactFiniteMeasureMeasurability

namespace OAI

/-! Positive modulus separates the actual compact-family majorant cost
from a constant functional. The separating functional is constructed. -/
open Set Filter MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}

lemma compactMeasureMajorantCost_const_lower
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val))
    (r : ℝ) : r*c ≤ compactMeasureMajorantCost σ S
      (r • (⟨1,HasCompactSupport.of_compactSpace (1 : C(S,ℝ))⟩ : C_c(S,ℝ))) := by
  by_cases hr : r ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr hc.le).trans
      (compactMeasureMajorantCost_nonneg σ hS hne hz _)
  have hr : 0 < r := lt_of_not_ge hr
  apply le_compactMeasureMajorantCost σ hS hne hz
  intro f hf
  let g : Z →ᵇ ℝ := r⁻¹ • f
  have ha (v : S) : 1 ≤ ∫ z, g z ∂(v.val : Measure Z) := by
    have hv : r ≤ ∫ z, f z ∂(v.val : Measure Z) := by
      simpa [compactMeasureTestOperator] using hf v
    have hb := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hr.le)
    simpa [g,BoundedContinuousFunction.smul_apply,integral_const_mul,
      inv_mul_cancel₀ hr.ne'] using hb
  have hb := measureFamilyModulus_le_boundedContinuous_norm σ (fun v : S => v.val) g ha
  have hsq : c^2 < ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖^2 :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp (hmod.trans_le hb)).1
  have hlin : c < ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖ := by
    nlinarith [norm_nonneg (BoundedContinuousFunction.toLp 2 σ ℝ g)]
  have hnorm : ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖ =
      r⁻¹ * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    simp only [g,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  rw [hnorm] at hlin
  have hmul := mul_lt_mul_of_pos_left hlin hr
  have hmul' : r*c < ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hmul
  exact hmul'.le

lemma exists_compact_measure_separating_functional
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ Λ : C_c(S,ℝ) →ₚ[ℝ] ℝ,
      Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(S,ℝ))⟩ = c ∧
      ∀ u, Λ u ≤ compactMeasureMajorantCost σ S u := by
  let : Nonempty S := hne.to_subtype
  apply exists_compact_positive_functional_of_majorant_cost
    (compactMeasureMajorantCost σ S)
  · exact fun r hr u => compactMeasureMajorantCost_smul σ hS hne hz r hr u
  · exact compactMeasureMajorantCost_add σ hS hne hz
  · intro u hu
    exact compactMeasureMajorantCost_nonpos σ hS hne hz (-u) (fun v => by
      simpa using neg_nonpos.mpr (hu v))
  · exact compactMeasureMajorantCost_const_lower σ hS hne hz c hc hmod

lemma exists_compact_measure_test_plan [PolishSpace Z]
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ P : ProbabilityMeasure S, ∀ f : Z →ᵇ ℝ,
      c * (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
  obtain ⟨Λ,hΛ1,hΛ⟩ := exists_compact_measure_separating_functional σ hS hne hz c hc hmod
  let L : C_c(S,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (c⁻¹ • Λ.toLinearMap)
    (fun u hu => mul_nonneg (inv_nonneg.mpr hc.le) (Λ.map_nonneg hu))
  have hL1 : L ⟨1,HasCompactSupport.of_compactSpace (1 : C(S,ℝ))⟩ = 1 := by
    change c⁻¹ * Λ _ = 1
    rw [hΛ1,inv_mul_cancel₀ hc.ne']
  obtain ⟨P,hP⟩ := exists_probability_of_compact_positive_functional_trim
    (compact_finiteMeasure_measurable_le_borel S) L hL1
  refine ⟨P,?_⟩
  intro f
  let u : C_c(S,ℝ) := ⟨compactMeasureTestOperator S f,
    HasCompactSupport.of_compactSpace (compactMeasureTestOperator S f)⟩
  have hi : c * (∫ v : S, u v ∂(P : Measure S)) = Λ u := by
    rw [hP u ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe)]
    change c * (c⁻¹ * Λ u) = Λ u
    rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  have hb := (hΛ u).trans (compactMeasureMajorantCost_le σ u f (fun _ => le_rfl))
  rw [← hi] at hb
  exact hb

end CircleDomainRigidity

end

end OAI
