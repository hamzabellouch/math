import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullEisensteinFourier

namespace OAI

/-! Initial normalization of the full positive-height Fourier observable. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPositiveRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ)) (ε : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Ioi ε,star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3

lemma cubicThetaPositiveFourierObservable_iterated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 3<s.re) :
    cubicThetaPositiveFourierObservable h W hε hW s=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,star (cubicThetaHorizontalCharacter h z)*
          cubicThetaEisenstein (z,v) s := by
  rw [cubicThetaPositiveFourierObservable_right h W hε hW hs]
  have he := cubicThetaFourierStripSeed_pair_on_strip h W hε hW
    (cubicThetaEisensteinSection s (by linarith))
  change (∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaEisenstein p.val s
    ∂cubicThetaPointMeasure)=_ at he
  rw [he]
  have hi := cubicThetaPositiveFourierPairing_integrable h W hε hW
    (cubicThetaEisensteinSection s (by linarith))
  have hf := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaEisenstein y s) hi
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaEisenstein p.val s
      ∂cubicThetaPointMeasure)=_ at hf
  change (∫ p in cubicThetaCuspStrip ε,star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
    cubicThetaEisenstein p.val s ∂cubicThetaPointMeasure)=_
  rw [hf]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  dsimp only
  rw [star_mul]
  ring

theorem cubicThetaPositiveFourierObservable_normalized {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaPositiveFourierObservable h W hε hW s=
      ((Real.pi:ℂ)/Complex.Gamma s)*cubicThetaFrequencyDirichlet h s*
        cubicThetaPositiveRadialTest h W ε s := by
  rw [cubicThetaPositiveFourierObservable_iterated h W hε hW hs,
    cubicThetaPositiveRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaEisenstein_horizontal_coefficient (hε.trans hv) (by linarith) hh]
  have hphase : (Real.fourierChar (tracePair 0 (cubicThetaRowFrequency h)):ℂ)=1 := by
    simp [tracePair]
  simp only [cubicThetaNonzeroFrequencyTerm,ite_eq_right hh,hphase,mul_one,Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))*
        (star (W v)*(v:ℂ)^s*
          (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3)/
            Complex.Gamma s*cubicThetaFrequencyDirichlet h s := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
