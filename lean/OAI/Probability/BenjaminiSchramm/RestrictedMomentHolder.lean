import OAI.Probability.BenjaminiSchramm.LayerMomentDecomposition

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

lemma restricted_fractional_moment_holder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Set Ω) (X : Ω → ℝ≥0∞) (hX : Measurable X)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫⁻ ω in B, X ω^a ∂μ) ≤ (∫⁻ ω in B, X ω ∂μ)^a*(μ B)^(1-a) := by
  have hc := Real.holderConjugate_one_div ha (sub_pos.mpr ha1) (by ring : a+(1-a)=1)
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hc
    ((hX.pow_const a).aemeasurable)
      (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) (μ.restrict B))
  have hcancel : a*(1/a)=1 := by field_simp
  have hinva : 1/(1/a)=a := by field_simp
  have hinvb : 1/(1/(1-a))=1-a := by field_simp
  simpa only [Pi.mul_apply,mul_one,ENNReal.one_rpow,←ENNReal.rpow_mul,hcancel,ENNReal.rpow_one,
    lintegral_const,Measure.restrict_apply_univ,one_mul,hinva,hinvb] using hh

end Percolation.BenjaminiSchramm

end

end OAI
