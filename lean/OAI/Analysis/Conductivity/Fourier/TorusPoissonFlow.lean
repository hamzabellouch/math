import Mathlib
import OAI.Analysis.Conductivity.Sobolev.L2SpectralMultiplier
import OAI.Analysis.Conductivity.Geometry.TorusExponential

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance torusPoissonFlowMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

abbrev TorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

lemma poissonMultiplier_bound (s : Fin 3 → ℝ) (t : ℝ) (h : Fin 2 → ℤ) :
    ‖(Real.exp (-torusRate s h*|t|):ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg _)) (abs_nonneg _)

def torusPoissonFlow (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) : TorusL2 :=
    (mFourierBasis (d:=Fin 2)).repr.symm
      (sequenceMultiplier (fun h => (Real.exp (-torusRate s h*|t|):ℂ)) 1
        zero_le_one (poissonMultiplier_bound s t) ((mFourierBasis (d:=Fin 2)).repr f))

lemma torusPoissonFlow_coeff (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (torusPoissonFlow s t f) h=
      (Real.exp (-torusRate s h*|t|):ℂ)*mFourierCoeff f h := by
  rw [←mFourierBasis_repr,torusPoissonFlow,LinearIsometryEquiv.apply_symm_apply,
    sequenceMultiplier_apply,mFourierBasis_repr]

lemma torusPoissonFlow_zero (s : Fin 3 → ℝ) (f : TorusL2) : torusPoissonFlow s 0 f=f := by
  apply (mFourierBasis (d:=Fin 2)).repr.injective
  ext h
  rw [mFourierBasis_repr,torusPoissonFlow_coeff]
  simp only [abs_zero,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul]
  exact (mFourierBasis_repr f h).symm

lemma torusPoissonFlow_tendsto (s : Fin 3 → ℝ) (f : TorusL2) :
    Tendsto (fun t => torusPoissonFlow s t f) (𝓝 0) (𝓝 f) := by
  have hm : ∀ h : Fin 2 → ℤ,
      Tendsto (fun t : ℝ => (Real.exp (-torusRate s h*|t|):ℂ)) (𝓝 0) (𝓝 1) := by
    intro h
    have hc : Continuous (fun t : ℝ => (Real.exp (-torusRate s h*|t|):ℂ)) := by fun_prop
    simpa using hc.continuousAt.tendsto (x:=0)
  have hh := sequenceMultiplier_coeff_tendsto
    (fun t h => (Real.exp (-torusRate s h*|t|):ℂ)) 1 zero_le_one
    (poissonMultiplier_bound s) hm ((mFourierBasis (d:=Fin 2)).repr f)
  simpa only [Function.comp_def,torusPoissonFlow,LinearIsometryEquiv.symm_apply_apply] using
    (mFourierBasis (d:=Fin 2)).repr.symm.continuous.continuousAt.tendsto.comp hh

lemma torusFourierCoeff_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    ‖mFourierCoeff f h‖≤‖f‖ := by
  rw [←mFourierBasis_repr]
  exact (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) _ h).trans_eq
    ((mFourierBasis (d:=Fin 2)).repr.norm_map f)

lemma torusPoissonFlow_norm (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) :
    ‖torusPoissonFlow s t f‖≤‖f‖ := by
  unfold torusPoissonFlow
  rw [LinearIsometryEquiv.norm_map]
  apply ((sequenceMultiplier _ 1 zero_le_one (poissonMultiplier_bound s t)).le_opNorm _).trans
  have hm := sequenceMultiplier_norm _ 1 zero_le_one (poissonMultiplier_bound s t)
  simpa only [one_mul,LinearIsometryEquiv.norm_map] using
    mul_le_mul_of_nonneg_right hm (norm_nonneg ((mFourierBasis (d:=Fin 2)).repr f))

end ScalarConductivity

end

end OAI
