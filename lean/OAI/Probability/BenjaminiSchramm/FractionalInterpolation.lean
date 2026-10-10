import OAI.Probability.BenjaminiSchramm.FractionalHolder

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

theorem lintegral_rpow_interpolation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (a b θ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∫⁻ ω, X ω^((1-θ)*a+θ*b) ∂μ) ≤
      (∫⁻ ω, X ω^a ∂μ)^(1-θ)*(∫⁻ ω, X ω^b ∂μ)^θ := by
  by_cases hθ0 : θ=0
  · simp only [hθ0,sub_zero,one_mul,zero_mul,add_zero,ENNReal.rpow_one,
      ENNReal.rpow_zero,mul_one,le_refl]
  by_cases hθeq1 : θ=1
  · simp only [hθeq1,sub_self,zero_mul,one_mul,zero_add,ENNReal.rpow_one,
      ENNReal.rpow_zero,le_refl]
  have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
  have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθeq1
  have hholder : (1/(1-θ)).HolderConjugate (1/θ) :=
    Real.holderConjugate_one_div (sub_pos.mpr hθlt) hθpos (by ring)
  have hca : ((1-θ)*a)*(1/(1-θ))=a := by
    field_simp [ne_of_gt (sub_pos.mpr hθlt)]
  have hcb : (θ*b)*(1/θ)=b := by field_simp [hθ0]
  have hia : 1/(1/(1-θ))=1-θ := by field_simp
  have hib : 1/(1/θ)=θ := by field_simp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hholder
    ((hX.pow_const ((1-θ)*a)).aemeasurable)
    ((hX.pow_const (θ*b)).aemeasurable)
  simp only [Pi.mul_apply,←ENNReal.rpow_mul,hca,hcb,hia,hib] at hh
  calc
    _ = ∫⁻ ω, X ω^((1-θ)*a)*X ω^(θ*b) ∂μ := by
      apply lintegral_congr
      intro ω
      exact ENNReal.rpow_add_of_nonneg _ _
        (mul_nonneg (sub_nonneg.mpr hθ1) ha) (mul_nonneg hθ hb)
    _ ≤ _ := hh

end Percolation.BenjaminiSchramm

end

end OAI
