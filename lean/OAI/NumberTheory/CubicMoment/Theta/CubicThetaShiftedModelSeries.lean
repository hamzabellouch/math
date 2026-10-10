import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedCoefficientNormalization

namespace OAI

/-! The absolutely convergent arithmetic series determined by the proved
other-cusp coefficients. Its constant coefficient is explicitly zero. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaShiftedFrequency_third (h : Eisenstein) :
    cubicThetaShiftedRowFrequency h=cubicThetaRowFrequency h/3 := by
  unfold cubicThetaShiftedRowFrequency cubicThetaRowFrequency
  field_simp [traceLambda_ne_zero]
  ring

lemma cubicThetaShiftedNormalizedCoefficient_bound (n : ℤ) {h : Eisenstein} (hh : h≠0) :
    ‖cubicThetaShiftedNormalizedCoefficient n h‖≤243*‖cubicThetaArithmeticBaseScalar‖ := by
  rw [cubicThetaShiftedNormalizedCoefficient_explicit n hh]
  split_ifs
  · rw [norm_mul,norm_mul,Complex.norm_ofNat]
    calc
      _ ≤ (3*‖cubicThetaArithmeticBaseScalar‖)*81 :=
        mul_le_mul_of_nonneg_left (cubicThetaArithmeticCoefficient_norm_le _)
          (mul_nonneg (by norm_num) (_root_.norm_nonneg _))
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

def cubicThetaShiftedBareTerm (v : ℝ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v)

lemma cubicThetaShiftedBareTerm_summable {v : ℝ} (hv : 0<v) :
    Summable (cubicThetaShiftedBareTerm v) := by
  have hc : ∀ k : Eisenstein,k≠0 → ‖(1:ℂ)‖≤1*norm k := by
    intro k hk
    simpa only [norm_one,one_mul] using one_le_norm hk
  have hs := (cubicThetaSeries_summable (by norm_num : (0:ℝ)≤1) hc
    (div_pos hv (by norm_num : (0:ℝ)<3)) (0:ℂ)).comp_injective cubicThetaRowIndex_injective
  apply hs.congr
  intro h
  by_cases hh : h=0
  · simp [hh,cubicThetaSeriesTerm,cubicThetaShiftedBareTerm]
  · have hn := mul_ne_zero (neg_ne_zero.mpr lambdaE_prime.ne_zero) hh
    simp only [Function.comp_def,cubicThetaSeriesTerm,ite_eq_right hn,one_mul,
      cubicThetaShiftedBareTerm,ite_eq_right hh,cubicThetaRowFrequency_index,
      tracePair,mul_zero,Complex.zero_re,AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
    rw [cubicThetaShiftedFrequency_third,norm_div,Complex.norm_ofNat]
    congr 1
    ring

def cubicThetaShiftedModelTerm (n : ℤ) (v : ℝ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaShiftedNormalizedCoefficient n h*
    cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v)

lemma cubicThetaShiftedModelTerm_summable (n : ℤ) {v : ℝ} (hv : 0<v) :
    Summable (cubicThetaShiftedModelTerm n v) := by
  have hs := ((cubicThetaShiftedBareTerm_summable hv).norm).mul_left
    (243*‖cubicThetaArithmeticBaseScalar‖)
  apply Summable.of_norm_bounded hs
  intro h
  by_cases hh : h=0
  · simp only [hh,cubicThetaShiftedModelTerm,cubicThetaShiftedBareTerm,ite_true,norm_zero,mul_zero,le_refl]
  · simp only [cubicThetaShiftedModelTerm,cubicThetaShiftedBareTerm,ite_eq_right hh,norm_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaShiftedNormalizedCoefficient_bound n hh)
      (_root_.norm_nonneg _)

def cubicThetaShiftedModelTorus (n : ℤ) (v : ℝ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein,cubicThetaShiftedModelTerm n v h • cubicThetaTorusFourier h

lemma cubicThetaShiftedModelTorus_summable (n : ℤ) {v : ℝ} (hv : 0<v) :
    Summable (fun h : Eisenstein => cubicThetaShiftedModelTerm n v h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using
    (cubicThetaShiftedModelTerm_summable n hv).norm

lemma cubicThetaShiftedModelTorus_coefficient (n : ℤ) {v : ℝ} (hv : 0<v) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaShiftedModelTorus n v)) k=
      cubicThetaShiftedModelTerm n v k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaShiftedModelTorus n v)=_
  rw [cubicThetaShiftedModelTorus,L.map_tsum (cubicThetaShiftedModelTorus_summable n hv),
    tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_eq_right hne.symm,
      smul_zero]

def cubicThetaShiftedModelSeries (n : ℤ) (z : ℂ) (v : ℝ) : ℂ :=
  ∑' h : Eisenstein,cubicThetaShiftedModelTerm n v h*
    (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)

lemma cubicThetaShiftedModelTorus_real (n : ℤ) {v : ℝ} (hv : 0<v) (x : Fin 2 → ℝ) :
    cubicThetaShiftedModelTorus n v (fun i => (x i:UnitAddCircle))=
      cubicThetaShiftedModelSeries n (3*cubicThetaPeriodCell x) v := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaShiftedModelTorus_summable n hv)
  change cubicThetaShiftedModelTorus n v (fun i => (x i:UnitAddCircle))=_ at he
  rw [he,cubicThetaShiftedModelSeries]
  apply tsum_congr
  intro h
  change cubicThetaShiftedModelTerm n v h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaShifted_frequency_cell]

end CubicFirstMoment

end

end OAI
