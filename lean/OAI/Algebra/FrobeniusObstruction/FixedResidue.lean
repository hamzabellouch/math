import Mathlib
import OAI.Algebra.FrobeniusObstruction.BlockTensor
import OAI.Algebra.FrobeniusObstruction.ResiduePairing
import OAI.Algebra.FrobeniusObstruction.NormalPrimitives

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.MixedForms
open scoped TensorProduct
variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
theorem coeff_mul_tmul (a b : A) (x : Ext (k := k) (ι := ι)) :
    coeff a * (b ⊗ₜ[k] x) = (a*b) ⊗ₜ[k] x := by
  simp only [coeff_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction.FixedResidue
open Frobenius MixedForms
open scoped TensorProduct
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (hell : 0 < ell)

abbrev Scalar := Frobenius.Ring (ι := ι) (k := k) ell
abbrev BScalar := Frobenius.Ring (ι := ι) (k := ThreeParameters.Ring k) ell

                                                                             
                                                                                
def scalar (v : Ext (k := k) (ι := ι) →ₗ[k] k) :
    Forms (k := k) (A := Scalar (ι := ι) (k := k) ell) (ι := ι) →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (quotientCoeff ell (topExponent ell) (topExponent_good hell)) v)

def parameter (v : Ext (k := k) (ι := ι) →ₗ[k] k) :
    Forms (k := k) (A := BScalar (ι := ι) (k := k) ell) (ι := ι) →ₗ[k] ThreeParameters.Ring k :=
  (TensorProduct.rid k (ThreeParameters.Ring k)).toLinearMap.comp
    (TensorProduct.map
      ((quotientCoeff (ι := ι) (k := ThreeParameters.Ring k) ell
        (topExponent ell) (topExponent_good hell)).restrictScalars k) v)

omit [DecidableEq ι] in
@[simp] theorem scalar_tmul (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (a : Scalar (ι := ι) (k := k) ell) (x : Ext (k := k) (ι := ι)) :
    scalar ell hell v (a ⊗ₜ[k] x) =
      quotientCoeff ell (topExponent ell) (topExponent_good hell) a * v x := rfl

omit [DecidableEq ι] in
@[simp] theorem parameter_tmul (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (a : BScalar (ι := ι) (k := k) ell) (x : Ext (k := k) (ι := ι)) :
    parameter ell hell v (a ⊗ₜ[k] x) =
      (v x) • quotientCoeff ell (topExponent ell) (topExponent_good hell) a := rfl

omit [DecidableEq ι] in
theorem parameter_coeff_mul (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (b : ThreeParameters.Ring k)
    (x : Forms (k := k) (A := BScalar (ι := ι) (k := k) ell) (ι := ι)) :
    parameter ell hell v (coeff (@algebraMap (ThreeParameters.Ring k)
      (BScalar (ι := ι) (k := k) ell) inferInstance inferInstance inferInstance b) * x) = b * parameter ell hell v x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | tmul a x =>
    rw [coeff_mul_tmul, parameter_tmul, parameter_tmul]
    rw [← Algebra.smul_def, map_smul]
    exact smul_comm (v x) b _

omit [DecidableEq ι] in
theorem topCoeff_reduction (x : BScalar (ι := ι) (k := k) ell) :
    ThreeParameters.augmentation k
      (quotientCoeff ell (topExponent ell) (topExponent_good hell) x) =
      quotientCoeff ell (topExponent ell) (topExponent_good hell) (reduction ell x) := by
  induction x using Quotient.inductionOn with
  | h f =>
    change ThreeParameters.augmentation k (MvPowerSeries.coeff (topExponent ell) f) =
      MvPowerSeries.coeff (topExponent ell)
        (MvPowerSeries.map (ThreeParameters.augmentation k) f)
    simp only [MvPowerSeries.coeff_map]

omit [DecidableEq ι] in
theorem reduction_parameter (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (x : Forms (k := k) (A := BScalar (ι := ι) (k := k) ell) (ι := ι)) :
    ThreeParameters.augmentation k (parameter ell hell v x) =
      scalar ell hell v (coefficientMap (reduction ell) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [parameter_tmul, coefficientMap_tmul, scalar_tmul]
    let f : ThreeParameters.Ring k →ₐ[k] k :=
      { ThreeParameters.augmentation k with
        commutes' := ThreeParameters.augmentation_algebraMap k }
    have hs := f.toLinearMap.map_smul (v x)
      (quotientCoeff ell (topExponent ell) (topExponent_good hell) a)
    change ThreeParameters.augmentation k (v x • _) =
      v x • ThreeParameters.augmentation k (quotientCoeff ell (topExponent ell)
        (topExponent_good hell) a) at hs
    rw [hs, topCoeff_reduction ell hell]
    exact mul_comm _ _

 theorem mul_delta_of_cycle {A : Type*} [CommRing A] [Algebra k A]
    (pd : ι → Derivation k A A) (F : A)
    (x y : Forms (k := k) (A := A) (ι := ι)) (hy : delta pd F y = 0) :
    delta pd F x * y = 0 := by
  rw [delta_apply, gradient_supercommute, mul_assoc, ← delta_apply, hy, mul_zero]

omit [DecidableEq ι] in
theorem parameter_pair_isUnit
    (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (x : Forms (k := k) (A := BScalar (ι := ι) (k := k) ell) (ι := ι))
    (hx : scalar ell hell v (coefficientMap (reduction ell) x) ≠ 0) :
    IsUnit (parameter ell hell v x) := by
  apply ThreeParameters.isUnit_of_augmentation_ne_zero k
  rwa [reduction_parameter ell hell v]

theorem residue_zero_of_w_boundary
    (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (pd : ι → Derivation k (BScalar (ι := ι) (k := k) ell)
      (BScalar (ι := ι) (k := k) ell)) (F : BScalar (ι := ι) (k := k) ell)
    (alpha beta eta : Forms (k := k) (A := BScalar (ι := ι) (k := k) ell) (ι := ι))
    (hbeta : delta pd F beta = 0)
    (heta : delta pd F eta =
      coeff (@algebraMap (ThreeParameters.Ring k) (BScalar (ι := ι) (k := k) ell)
        inferInstance inferInstance inferInstance (ThreeParameters.w k)) * alpha) :
    ThreeParameters.w k * parameter ell hell v (alpha * beta) = 0 := by
  have hz : delta pd F eta * beta = 0 := by
    rw [delta_apply, gradient_supercommute, mul_assoc, ← delta_apply, hbeta, mul_zero]
  rw [heta, mul_assoc] at hz
  have hr := congrArg (parameter ell hell v) hz
  rw [parameter_coeff_mul ell hell v, map_zero] at hr
  exact hr

                                                                          
                                                                        
theorem unit_residue_contradiction
    (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (pd : ι → Derivation k (BScalar (ι := ι) (k := k) ell)
      (BScalar (ι := ι) (k := k) ell)) (F : BScalar (ι := ι) (k := k) ell)
    (alpha beta eta : Forms (k := k) (A := BScalar (ι := ι) (k := k) ell) (ι := ι))
    (hbeta : delta pd F beta = 0)
    (heta : delta pd F eta =
      coeff (@algebraMap (ThreeParameters.Ring k) (BScalar (ι := ι) (k := k) ell)
        inferInstance inferInstance inferInstance (ThreeParameters.w k)) * alpha)
    (hpair : scalar ell hell v (coefficientMap (reduction ell) (alpha * beta)) ≠ 0) : False := by
  have hu := parameter_pair_isUnit ell hell v (alpha * beta) hpair
  have hz := residue_zero_of_w_boundary ell hell v pd F alpha beta eta hbeta heta
  exact ThreeParameters.w_ne_zero k ((hu.mul_left_eq_zero).mp hz)

end BoundaryOnly.FormalObstruction.FixedResidue

end

end OAI
