import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedCusp

namespace OAI

/-! Nonzero Fourier observations at the inverted cusp retain the exact
primary Dirichlet coefficient and the original radial normalization. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaInvertedTorus_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaInvertedTorus v s)) h=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaInvertedNonzeroTerm (0,v) s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaInvertedTorus v s)=_
  rw [cubicThetaInvertedTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
    ite_eq_right hh,cubicThetaInvertedTorusRemainder_coefficient hv hs,smul_eq_mul,mul_zero,zero_add]

lemma cubicThetaInverted_horizontal_coefficient {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) {h : Eisenstein} (hh : h≠0) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)=
      (9*Real.sqrt 3/2:ℝ) •
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
          cubicThetaInvertedNonzeroTerm (0,v) s h) := by
  rw [cubicThetaHorizontalCoefficient
    (fun z => cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)
    (cubicThetaInvertedTorus v s) h (fun x => (cubicThetaInvertedTorus_real hv hs x).symm),
    cubicThetaInvertedTorus_coefficient hv hs hh]

def cubicThetaInvertedFourierObservable (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  cubicThetaInvertedCuspObservable (cubicThetaCuspFourierTest h W) s

lemma cubicThetaInvertedFourier_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W) (cubicThetaInvertedForcedCusp s)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    cubicThetaInvertedForcedCusp_coe hs] with p hp hE
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) _=_
  rw [hp,hE,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaInvertedFourierObservable_right (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedFourierObservable h W s=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaInvertedFourierObservable,cubicThetaInvertedCuspObservable,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    cubicThetaInvertedForcedCusp_coe hs] with p hp hE
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) _=_
  rw [hp,hE,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaInvertedFourierObservable_iterated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedFourierObservable h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaEisenstein
              (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s := by
  rw [cubicThetaInvertedFourierObservable_right h W hs]
  have hf := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y) s)
    (cubicThetaInvertedFourier_integrable h W hs)
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
    ∂cubicThetaPointMeasure)=_ at hf
  rw [hf]
  apply integral_congr_ae
  filter_upwards with v
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [star_mul]
  ring

theorem cubicThetaInvertedFourierObservable_normalized {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 3<s.re) :
    cubicThetaInvertedFourierObservable h W s=
      ((Real.pi:ℂ)/Complex.Gamma s)*cubicThetaInvertedFrequencyDirichlet h s*
        cubicThetaFourierRadialTest h W s := by
  rw [cubicThetaInvertedFourierObservable_iterated h W hs,cubicThetaFourierRadialTest,
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaInverted_horizontal_coefficient (by have h:=hv; change 2<v at h; linarith)
    (by linarith) hh]
  have hphase : (Real.fourierChar (tracePair 0 (cubicThetaRowFrequency h)):ℂ)=1 := by simp [tracePair]
  simp only [cubicThetaInvertedNonzeroTerm,ite_eq_right hh,hphase,mul_one,Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))*
        (star (W v)*(v:ℂ)^s*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3)/
            Complex.Gamma s*cubicThetaInvertedFrequencyDirichlet h s := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
