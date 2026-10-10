import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticRowSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCoefficient

namespace OAI

/-! Continuous torus realization of the explicit arithmetic theta series.
The nonconstant scalar is retained while its normalization is established. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaArithmeticModelTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaArithmeticModelTorusProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def cubicThetaArithmeticModelRemainder (v : ℝ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein,cubicThetaArithmeticRowTerm 0 v h • cubicThetaTorusFourier h

lemma cubicThetaArithmeticModelRemainder_summable {v : ℝ} (hv : 0<v) :
    Summable (fun h : Eisenstein =>
      cubicThetaArithmeticRowTerm 0 v h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using
    (cubicThetaArithmeticRowTerm_summable 0 hv).norm

lemma cubicThetaArithmeticModelRemainder_real {v : ℝ} (hv : 0<v) (x : Fin 2 → ℝ) :
    cubicThetaArithmeticModelRemainder v (fun i => (x i:UnitAddCircle))=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (cubicThetaPeriodCell x,v) := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaArithmeticModelRemainder_summable hv)
  change cubicThetaArithmeticModelRemainder v (fun i => (x i:UnitAddCircle))=_ at he
  rw [he,cubicThetaArithmeticRowSeries]
  apply tsum_congr
  intro h
  change cubicThetaArithmeticRowTerm 0 v h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,←cubicThetaArithmeticRowTerm_phase]

lemma cubicThetaArithmeticModelRemainder_coefficient {v : ℝ} (hv : 0<v) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaArithmeticModelRemainder v)) k=cubicThetaArithmeticRowTerm 0 v k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaArithmeticModelRemainder v)=_
  rw [cubicThetaArithmeticModelRemainder,L.map_tsum
    (cubicThetaArithmeticModelRemainder_summable hv),tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,
      smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

def cubicThetaArithmeticModel (A : ℂ) (p : ℂ × ℝ) : ℂ :=
  (cubicThetaConstant*p.2^(2/3:ℝ):ℝ)+
    A*cubicThetaNonconstant cubicThetaArithmeticCoefficient p

def cubicThetaArithmeticModelTorus (A : ℂ) (v : ℝ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ) • cubicThetaTorusFourier 0+
    A • cubicThetaArithmeticModelRemainder v

lemma cubicThetaArithmeticModelTorus_real (A : ℂ) {v : ℝ} (hv : 0<v) (x : Fin 2 → ℝ) :
    cubicThetaArithmeticModelTorus A v (fun i => (x i:UnitAddCircle))=
      cubicThetaArithmeticModel A (cubicThetaPeriodCell x,v) := by
  simp only [cubicThetaArithmeticModelTorus,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    cubicThetaTorusFourier_zero,ContinuousMap.one_apply,smul_eq_mul,mul_one,
    cubicThetaArithmeticModelRemainder_real hv,cubicThetaArithmeticModel]

theorem cubicThetaArithmeticModelTorus_coefficient (A : ℂ) {v : ℝ} (hv : 0<v)
    (h : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaArithmeticModelTorus A v)) h=
      if h=0 then ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)
      else A*cubicThetaArithmeticCoefficient (-lambdaE*h)*
        cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v) := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaArithmeticModelTorus A v)=_
  rw [cubicThetaArithmeticModelTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
    cubicThetaArithmeticModelRemainder_coefficient hv,smul_eq_mul]
  by_cases hh : h=0
  · simp [hh,cubicThetaArithmeticRowTerm]
  · simp [hh,cubicThetaArithmeticRowTerm,tracePair,mul_assoc]

end CubicFirstMoment

end

end OAI
