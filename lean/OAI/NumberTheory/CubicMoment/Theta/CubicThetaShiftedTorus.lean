import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedCoefficients
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticTorus

namespace OAI

/-! The actual continuous Fourier expansion at a translated cusp,
parametrized by its period-nine torus. All frequencies, including zero,
are retained until the explicit arithmetic support is applied. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def cubicThetaShiftedFourierTerm (b : Eisenstein) (v : ℝ) (s : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaShiftedFrequencyDirichlet b h s*
    ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t

lemma cubicThetaShiftedFourierTerm_summable (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) : Summable (cubicThetaShiftedFourierTerm b v s) := by
  have he := cubicThetaShiftedFourierCoefficients_summable b (p:=(0,v)) hv hs
  change Summable (fun h => cubicThetaShiftedFrequencyDirichlet b h s*
    ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)
  simpa only [tracePair,zero_mul,Complex.zero_re,mul_zero,AddChar.map_zero_eq_one,
    Circle.coe_one,mul_one] using he

def cubicThetaShiftedTorusSeries (b : Eisenstein) (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein, cubicThetaShiftedFourierTerm b v s h • cubicThetaTorusFourier h

lemma cubicThetaShiftedTorusSeries_summable (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) : Summable (fun h : Eisenstein =>
      cubicThetaShiftedFourierTerm b v s h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using
    (cubicThetaShiftedFourierTerm_summable b hv hs).norm

lemma cubicThetaShifted_frequency_cell (x : Fin 2 → ℝ) (h : Eisenstein) :
    tracePair (3*cubicThetaPeriodCell x) (cubicThetaShiftedRowFrequency h)=
      tracePair (cubicThetaPeriodCell x) (cubicThetaRowFrequency h) := by
  unfold tracePair cubicThetaShiftedRowFrequency cubicThetaRowFrequency
  congr 2
  ring

lemma cubicThetaShiftedTorusSeries_real (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (x : Fin 2 → ℝ) :
    cubicThetaShiftedTorusSeries b v s (fun i => (x i:UnitAddCircle))=
      ∑' h : Eisenstein, cubicThetaShiftedFrequencyDirichlet b h s*
        (Real.fourierChar (tracePair (3*cubicThetaPeriodCell x) (cubicThetaShiftedRowFrequency h)):ℂ)*
        ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaShiftedTorusSeries_summable b hv hs)
  change cubicThetaShiftedTorusSeries b v s (fun i => (x i:UnitAddCircle))=_ at he
  rw [he]
  apply tsum_congr
  intro h
  change cubicThetaShiftedFourierTerm b v s h*cubicThetaTorusFourier h
    (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaShifted_frequency_cell]
  unfold cubicThetaShiftedFourierTerm
  ring

def cubicThetaShiftedTorus (b : Eisenstein) (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s) •
    cubicThetaShiftedTorusSeries b v s

lemma cubicThetaShiftedTorus_real (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (x : Fin 2 → ℝ) :
    cubicThetaShiftedTorus b v s (fun i => (x i:UnitAddCircle))=
      cubicThetaEisenstein
        ((cubicThetaInversion 1 (3*cubicThetaPeriodCell x,v)).1+b,
          (cubicThetaInversion 1 (3*cubicThetaPeriodCell x,v)).2) s := by
  rw [cubicThetaEisenstein_shifted_fourier_normalized b hv hs]
  simp only [cubicThetaShiftedTorus,ContinuousMap.smul_apply,smul_eq_mul,
    cubicThetaShiftedTorusSeries_real b hv hs]

lemma cubicThetaShiftedTorusSeries_coefficient (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaShiftedTorusSeries b v s)) k=cubicThetaShiftedFourierTerm b v s k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaShiftedTorusSeries b v s)=_
  rw [cubicThetaShiftedTorusSeries,L.map_tsum (cubicThetaShiftedTorusSeries_summable b hv hs)]
  rw [tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

end CubicFirstMoment

end

end OAI
