import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowTranslationEquiv
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierProfile
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDomain

namespace OAI

/-! A single half-open strip seed for the full Fourier Poincare sum.
Its translations have exactly one contributing term at every point. -/
noncomputable section
open Set
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaFourierStripSeed (h : Eisenstein) (W : C_c(ℝ,ℂ)) (p : CubicThetaPoint) : ℂ :=
  if p.val.1∈cubicThetaHorizontalCell then W p.val.2*cubicThetaHorizontalCharacter h p.val.1 else 0

lemma cubicThetaHorizontalCell_unique_eisenstein (z : ℂ) :
    ∃! w : Eisenstein,z+3*(w:ℂ)∈cubicThetaHorizontalCell := by
  obtain ⟨g,hg,huniq⟩ := cubicThetaHorizontalCell_unique z
  refine ⟨Multiplicative.toAdd g,hg,?_⟩
  intro w hw
  have he := huniq (Multiplicative.ofAdd w) hw
  exact congrArg Multiplicative.toAdd he

lemma cubicThetaFourierStripSeed_translate (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaFourierStripSeed h W (cubicThetaPrincipalTranslation w • p)=
      if p.val.1+3*(w:ℂ)∈cubicThetaHorizontalCell then
        W p.val.2*cubicThetaHorizontalCharacter h p.val.1 else 0 := by
  unfold cubicThetaFourierStripSeed
  have he := cubicThetaPrincipalTranslation_coordinates w p
  change (cubicThetaPrincipalTranslation w • p).val=(p.val.1+3*(w:ℂ),p.val.2) at he
  rw [he,cubicThetaHorizontalCharacter_periodic]

lemma cubicThetaFourierStripSeed_translation_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (p : CubicThetaPoint) :
    (∑' w : Eisenstein,cubicThetaFourierStripSeed h W (cubicThetaPrincipalTranslation w • p))=
      W p.val.2*cubicThetaHorizontalCharacter h p.val.1 := by
  classical
  obtain ⟨w,hw,huniq⟩ := cubicThetaHorizontalCell_unique_eisenstein p.val.1
  rw [tsum_eq_single w]
  · rw [cubicThetaFourierStripSeed_translate,ite_eq_left hw]
  · intro v hv
    rw [cubicThetaFourierStripSeed_translate]
    apply ite_eq_right
    intro hm
    exact hv (huniq v hm)

lemma cubicThetaFourierStripSeed_pair_translation_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (F : CubicThetaSection) (p : CubicThetaPoint) :
    (∑' w : Eisenstein,star (cubicThetaFourierStripSeed h W (cubicThetaPrincipalTranslation w • p))*
      F.val (cubicThetaPrincipalTranslation w • p))=
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val p := by
  have he (w : Eisenstein) : F.val (cubicThetaPrincipalTranslation w • p)=F.val p := by
    have hh := F.property (cubicThetaPrincipalTranslation w) p
    change F.val (cubicThetaPrincipalTranslation w • p)=
      cubicThetaKubotaValue (cubicThetaPrincipalTranslation w)*F.val p at hh
    simpa only [cubicThetaPrincipalTranslation_value,one_mul] using hh
  simp_rw [he]
  rw [tsum_mul_right,←tsum_star,cubicThetaFourierStripSeed_translation_sum]

end CubicFirstMoment

end

end OAI
