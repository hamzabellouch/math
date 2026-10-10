import Mathlib

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
noncomputable def total : ℝ := ∫ x, ρ x ∂μ
noncomputable def probability : Measure α := μ.withDensity (fun x => ENNReal.ofReal (ρ x / total μ ρ))
lemma isProbability (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (hW : 0 < total μ ρ) :
    IsProbabilityMeasure (probability μ ρ) := by
  constructor
  rw [probability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (hρ.mono fun x hx => div_nonneg hx hW.le)]
  rw [integral_div]
  change ENNReal.ofReal (total μ ρ / total μ ρ) = 1
  rw [div_self hW.ne',ENNReal.ofReal_one]
lemma integral_probability (hi : AEStronglyMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ)
    (hW : 0 < total μ ρ) (f : α → ℝ) :
    (∫ x, f x ∂probability μ ρ) = (∫ x, ρ x*f x ∂μ)/total μ ρ := by
  rw [probability,integral_withDensity_eq_integral_toReal_smul₀
    (hi.aemeasurable.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hW.le),smul_eq_mul]
  ring
lemma ae_probability (h : ∀ᵐ x ∂μ, 0 ≤ ρ x) : ∀ᵐ x ∂probability μ ρ, 0 ≤ ρ x :=
  withDensity_absolutelyContinuous _ _ h
lemma integrable_probability {f : α → ℝ} (hi : AEStronglyMeasurable ρ μ)
    (hρ : 0 ≤ᵐ[μ] ρ) (hW : 0 < total μ ρ) (hf : AEStronglyMeasurable f μ)
    (hprod : Integrable (fun x => ρ x*f x) μ) : Integrable f (probability μ ρ) := by
  refine ⟨hf.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
  apply Integrable.hasFiniteIntegral
  rw [probability]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (hi.aemeasurable.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    ).mpr
  apply (hprod.div_const _).congr
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hW.le),smul_eq_mul]
  ring
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
lemma lintegral_probability (hρ : AEMeasurable ρ μ) (hW : 0 < total μ ρ)
    (F : α → ℝ≥0∞) (hF : AEMeasurable F μ) :
    ENNReal.ofReal (total μ ρ)*(∫⁻ x, F x ∂probability μ ρ) =
      ∫⁻ x, ENNReal.ofReal (ρ x)*F x ∂μ := by
  rw [probability,lintegral_withDensity_eq_lintegral_mul₀
    (hρ.div_const _).ennreal_ofReal hF,
    ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  dsimp only [Pi.mul_apply]
  rw [ENNReal.ofReal_div_of_pos hW,div_eq_mul_inv]
  calc
    _ = (ENNReal.ofReal (total μ ρ)*(ENNReal.ofReal (total μ ρ))⁻¹)*
        (ENNReal.ofReal (ρ x)*F x) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hW) ENNReal.ofReal_ne_top,one_mul]
end CAT0Fillings.ChordMeasure
end

end OAI
