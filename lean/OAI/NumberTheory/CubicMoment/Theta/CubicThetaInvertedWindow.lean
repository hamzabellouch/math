import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedIncoming
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedTorus

namespace OAI

/-! A bounded global observation of the inverted Eisenstein series.
The literal strip integral is evaluated by the previously proved physical mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaInvertedWindowTest : cubicThetaSmoothTests :=
  cubicThetaInversionSmooth (cubicThetaHighWindowTest (4/3))

def cubicThetaInvertedWindowObservable (s : ℂ) : ℂ :=
  cubicThetaArithmeticDistribution cubicThetaInvertedWindowTest
    cubicThetaInvertedWindowTest.property.2 s

lemma cubicThetaInvertedWindowObservable_meromorphic {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt cubicThetaInvertedWindowObservable s :=
  cubicThetaArithmeticDistribution_meromorphic _ cubicThetaInvertedWindowTest.property.2 hs

lemma cubicThetaInvertedWindowObservable_right {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedWindowObservable s=
      ∫ p in cubicThetaCuspStrip 2,
        star (cubicThetaHighWindowForcing (4/3) p.val.2)*cubicThetaEisenstein
          (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
        ∂cubicThetaPointMeasure := by
  let F := cubicThetaArithmeticSection s (show 2<s.re by linarith)
  have hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure :=
    cubicThetaArithmeticSection_memLp hs
  have hI := cubicThetaInversionSection_memLp F hF
  rw [cubicThetaInvertedWindowObservable,cubicThetaArithmeticDistribution_right _ _ hs]
  change (∫ q, cubicThetaSectionPairing
    (cubicThetaInversionSection (cubicThetaHighWindowSection (4/3))) F q
      ∂cubicThetaQuotientMeasure)=_
  rw [cubicThetaInversion_pairing_integral]
  have hp := cubicThetaSectionPairing_L2 (cubicThetaHighWindowSection (4/3))
    (cubicThetaInversionSection F)
    (cubicThetaCompactSection_memLp _ (cubicThetaHighWindowSection_compact (4/3))) hI
  rw [←hp]
  change inner ℂ (cubicThetaHighWindowL2 (4/3)) (hI.toLp _)=_
  rw [cubicThetaHighWindowPairing_section (4/3) _ hI]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  have hheight : 1<p.val.2 := by have h:=hp.1; change 2<p.val.2 at h; linarith
  change inner ℂ (cubicThetaHighWindowForcing (4/3) p.val.2)
    (cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s)=_
  rw [cubicThetaArithmeticRemainder_inverted hheight]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

lemma cubicThetaInvertedWindow_integrable {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (cubicThetaHighWindowForcing (4/3) p.val.2)*cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hW := cubicThetaCuspFourierWeight_memLp 0 (cubicThetaHighWindowWeight (4/3))
  have hE := cubicThetaInvertedEisenstein_strip_memLp hs
  have hw : MemLp (fun p : CubicThetaPoint => cubicThetaHighWindowForcing (4/3) p.val.2) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
    change MemLp (fun p : CubicThetaPoint => cubicThetaHighWindowForcing (4/3) p.val.2*
      (Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency 0)):ℂ)) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) at hW
    simpa [cubicThetaRowFrequency,tracePair] using hW
  exact hw.star.integrable_mul hE

lemma cubicThetaInvertedWindowObservable_normalized {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedWindowObservable s=
      ((Real.pi:ℂ)/(s-1))*cubicThetaInvertedConstantContinuation s*
        cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) s := by
  rw [cubicThetaInvertedWindowObservable_right hs]
  have hf := cubicThetaCuspStrip_fubini
    (fun y => star (cubicThetaHighWindowForcing (4/3) y.2)*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y) s)
    (cubicThetaInvertedWindow_integrable hs)
  change (∫ p in cubicThetaCuspStrip 2,
    star (cubicThetaHighWindowForcing (4/3) p.val.2)*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
    ∂cubicThetaPointMeasure)=_ at hf
  rw [hf]
  rw [cubicThetaZeroRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  have he : (∫ z in cubicThetaHorizontalCell,
      star (cubicThetaHighWindowForcing (4/3) v)*cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s/(v:ℂ)^3)=
      (star (cubicThetaHighWindowForcing (4/3) v)/(v:ℂ)^3)*
        ∫ z in cubicThetaHorizontalCell, cubicThetaEisenstein
          (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [he,cubicThetaInverted_horizontal_mean (by linarith) (by linarith),
    cubicThetaInvertedConstantMode_eq (by linarith) (by linarith),
    cubicThetaInvertedConstantContinuation_right (by linarith),Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))/(s-1)*
        cubicThetaInvertedConstantContinuation s*
        (star (cubicThetaHighWindowForcing (4/3) v)*(v:ℂ)^(2-s)/(v:ℂ)^3) := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; rfl

end CubicFirstMoment

end

end OAI
