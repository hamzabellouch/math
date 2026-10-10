import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfilePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCharacterOrthogonality

namespace OAI

/-! The exact Gram pairing of compact high-cusp Fourier Poincare sources. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaFourierProfile_gram (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (hV : ∀ v≤(2:ℝ),V v=0) :
    inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaFourierProfileL2 k V hV)=
      inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspFourierTest k V) := by
  change inner ℂ (cubicThetaFourierProfileL2 h W hW)
    ((cubicThetaCompactSection_memLp _
      (cubicThetaFourierProfileSection_compact k V (fun v hv => hV v (by linarith)))).toLp _)=_
  rw [cubicThetaFourierProfilePairing_section,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaCuspFourierWeight_memLp k V).coeFn_toLp,
    ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp hq hstrip
  change _=inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
    (((cubicThetaCuspFourierWeight_memLp k V).toLp _) p)
  rw [hp,hq]
  change inner ℂ (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)
    (cubicThetaFourierProfileSeries k p.val V)=_
  rw [cubicThetaFourierProfileSeries_high k V (fun v hv => hV v (by linarith))
    (by have hh:=hstrip.1; change 2<p.val.2 at hh; linarith)]
  rfl

lemma cubicThetaCuspFourierTest_pairing (h k : Eisenstein) (W V : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspFourierTest k V)=
      ∫ v in Ioi (2:ℝ),star (W v)*V v/(v:ℂ)^3*
        cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k) := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W)
    (cubicThetaCuspFourierTest k V)
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
        (V p.val.2*cubicThetaHorizontalCharacter k p.val.1))
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaCuspFourierWeight_memLp k V).coeFn_toLp] with p hp hq
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
      (((cubicThetaCuspFourierWeight_memLp k V).toLp _) p)=_
    rw [hp,hq]
    simp only [RCLike.inner_apply',starRingEnd_apply,
      cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter]
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*
      (V y.2*cubicThetaHorizontalCharacter k y.1)) hi'
  have hp : inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspFourierTest k V)=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
          (V p.val.2*cubicThetaHorizontalCharacter k p.val.1) ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaCuspFourierWeight_memLp k V).coeFn_toLp] with p hp hq
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
      (((cubicThetaCuspFourierWeight_memLp k V).toLp _) p)=_
    rw [hp,hq]
    simp only [RCLike.inner_apply',starRingEnd_apply,
      cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter]
  dsimp only [cubicThetaPointCoordinates] at he
  rw [hp,he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

theorem cubicThetaFourierProfile_orthogonal {h k : Eisenstein} (hhk : h≠k)
    (W V : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ),W v=0) (hV : ∀ v≤(2:ℝ),V v=0) :
    inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaFourierProfileL2 k V hV)=0 := by
  rw [cubicThetaFourierProfile_gram,cubicThetaCuspFourierTest_pairing,
    cubicThetaHorizontalFourier_character_zero hhk]
  simp only [mul_zero,integral_zero]

end CubicFirstMoment

end

end OAI
