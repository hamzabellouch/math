import OAI.Probability.BenjaminiSchramm.LayerMomentDecomposition

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

lemma fractional_holder_with_count
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Ω → ℝ≥0∞) (hA : Measurable A) (hB : Measurable B)
    (hBfin : ∀ᵐ ω ∂μ, 1 ≤ B ω ∧ B ω ≠ ⊤)
    {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hδ : 0 ≤ δ) (hδa : δ ≤ 1-a) :
    (∫⁻ ω, A ω^a ∂μ) ≤
      (∫⁻ ω, A ω*B ω^(-δ) ∂μ)^a * (∫⁻ ω, B ω^a ∂μ)^δ := by
  by_cases hδ0 : δ=0
  · simpa only [hδ0,neg_zero,ENNReal.rpow_zero,mul_one] using
      ennreal_lintegral_rpow_le_rpow_lintegral μ A hA ha ha1.le
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have hc : (1/a).HolderConjugate (1/(1-a)) :=
    Real.holderConjugate_one_div ha (sub_pos.mpr ha1) (by ring)
  have hcancel : a*(1/a)=1 := by field_simp
  have hinva : 1/(1/a)=a := by field_simp
  have hinvb : 1/(1/(1-a))=1-a := by field_simp
  have hfactor : (fun ω => A ω^a) =ᵐ[μ]
      (fun ω => (A ω*B ω^(-δ))^a * B ω^(a*δ)) := by
    filter_upwards [hBfin] with ω hω
    have hne : B ω ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hω.1)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le,←ENNReal.rpow_mul,mul_assoc,
      ←ENNReal.rpow_add _ _ hne hω.2,
      show -δ*a+a*δ=0 by ring,ENNReal.rpow_zero,mul_one]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    (((hA.mul (hB.pow_const (-δ))).pow_const a).aemeasurable)
      ((hB.pow_const (a*δ)).aemeasurable)
  simp only [Pi.mul_apply,←ENNReal.rpow_mul,hcancel,ENNReal.rpow_one,hinva,hinvb] at hh
  have hb : 0 < δ/(1-a) := div_pos hδpos (sub_pos.mpr ha1)
  have hb1 : δ/(1-a) ≤ 1 := (div_le_one (sub_pos.mpr ha1)).mpr hδa
  have hj := ennreal_lintegral_rpow_le_rpow_lintegral μ (fun ω => B ω^a)
    (hB.pow_const a) hb hb1
  have he : a*δ*(1/(1-a))=a*(δ/(1-a)) := by ring
  have he' : δ/(1-a)*(1-a)=δ := by field_simp [ne_of_gt (sub_pos.mpr ha1)]
  calc
    _ = ∫⁻ ω, (A ω*B ω^(-δ))^a*B ω^(a*δ) ∂μ := lintegral_congr_ae hfactor
    _ ≤ (∫⁻ ω, A ω*B ω^(-δ) ∂μ)^a *
        (∫⁻ ω, B ω^(a*δ*(1/(1-a))) ∂μ)^(1-a) := hh
    _ ≤ (∫⁻ ω, A ω*B ω^(-δ) ∂μ)^a *
        ((∫⁻ ω, B ω^a ∂μ)^(δ/(1-a)))^(1-a) := by
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ (sub_nonneg.mpr ha1.le)
      simpa only [←ENNReal.rpow_mul,he] using hj
    _ = _ := by rw [←ENNReal.rpow_mul,he']

end Percolation.BenjaminiSchramm

end

end OAI
