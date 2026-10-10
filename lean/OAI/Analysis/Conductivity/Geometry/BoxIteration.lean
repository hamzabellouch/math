import Mathlib
import OAI.Analysis.Conductivity.Geometry.ExtendedCollar

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def threeArrow : (Fin 3 → ℝ) ≃ᵐ ℝ×(ℝ×ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.finTwoArrow))

lemma threeArrow_apply (x : Fin 3 → ℝ) : threeArrow x=(x 0,x 1,x 2) := by rfl
lemma threeArrow_symm_apply (x : ℝ×(ℝ×ℝ)) : threeArrow.symm x=![x.1,x.2.1,x.2.2] := by
  ext i; fin_cases i <;> rfl

lemma threeArrow_volume : MeasurePreserving threeArrow := by
  exact ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

lemma sourceExtendedBox_image (l r : ℝ) :
    threeArrow '' sourceExtendedBox l r=Icc l r ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
  ext z
  rw [MeasurableEquiv.image_eq_preimage_symm]
  simp [threeArrow_symm_apply,mem_sourceExtendedBox,abs_le,Prod.le_def]
  tauto

lemma integral_sourceExtendedBox {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g)
    {l r : ℝ} (hlr : l≤r) :
    (∫ x in sourceExtendedBox l r,g x)=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g ![t,a,b] := by
  have hc : Continuous (fun z : ℝ×(ℝ×ℝ) => g ![z.1,z.2.1,z.2.2]) := hg.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc l r ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)))
  have he := threeArrow_volume.setIntegral_image_emb threeArrow.measurableEmbedding
    (fun z : ℝ×(ℝ×ℝ) => g ![z.1,z.2.1,z.2.2]) (sourceExtendedBox l r)
  simp only [threeArrow_apply] at he
  have hid (x : Fin 3 → ℝ) : ![x 0,x 1,x 2]=x := by ext i; fin_cases i <;> rfl
  simp_rw [hid] at he
  have him := sourceExtendedBox_image l r
  simp only [threeArrow_apply] at him
  rw [←he,him]
  change (∫ y in Icc l r ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
    g ![y.1,y.2.1,y.2.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le hlr,
    intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact setIntegral_prod _ ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))

end ScalarConductivity

end

end OAI
