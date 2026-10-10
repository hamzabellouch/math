import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBranchPeriodicity

namespace OAI

/-! Continuous periodic horizontal slices of the actual automorphic
sections, with their genuine finite cell integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalPoint (v : ℝ) (hv : 0<v) (z : ℂ) : CubicThetaPoint := ⟨(z,v),hv⟩

lemma cubicThetaHorizontalPoint_continuous (v : ℝ) (hv : 0<v) :
    Continuous (cubicThetaHorizontalPoint v hv) := by
  apply Continuous.subtype_mk
  exact continuous_id.prodMk continuous_const

def cubicThetaSectionHorizontal (F : CubicThetaSection) (v : ℝ) (hv : 0<v) : C(ℂ,ℂ) :=
  ⟨fun z => F.val (cubicThetaHorizontalPoint v hv z),
    F.val.continuous.comp (cubicThetaHorizontalPoint_continuous v hv)⟩

lemma cubicThetaSectionHorizontal_periodic (F : CubicThetaSection) (v : ℝ) (hv : 0<v)
    (w : Eisenstein) (z : ℂ) :
    cubicThetaSectionHorizontal F v hv (z+3*(w:ℂ))=cubicThetaSectionHorizontal F v hv z := by
  have hp : cubicThetaHorizontalPoint v hv (z+3*(w:ℂ))=
      cubicThetaPrincipalTranslation w • cubicThetaHorizontalPoint v hv z := by
    apply Subtype.ext
    change (z+3*(w:ℂ),v)=cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) (z,v)
    rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
    push_cast
    rfl
  change F.val (cubicThetaHorizontalPoint v hv (z+3*(w:ℂ)))=_
  rw [hp,F.property,cubicThetaPrincipalTranslation_value,one_mul]
  rfl

lemma cubicThetaSectionHorizontal_integrable (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (cubicThetaSectionHorizontal F v hv) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact ((cubicThetaSectionHorizontal F v hv).continuous.continuousOn.integrableOn_compact hK).mono_set hsub

theorem cubicThetaSectionHorizontal_translate_integral (F : CubicThetaSection)
    (v : ℝ) (hv : 0<v) (a : ℂ) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F v hv (z+a))=
      ∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F v hv z :=
  cubicThetaHorizontal_translate_integral _ (cubicThetaSectionHorizontal_periodic F v hv) a

end CubicFirstMoment

end

end OAI
