import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalPureCocycle

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]
def coefficientUnit (v : Kˣ) : (RatFunc K)ˣ := Units.map RatFunc.C.toMonoidHom v
def variableUnit : (RatFunc K)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
@[simp] lemma coefficientUnit_val (v : Kˣ) : (coefficientUnit v:RatFunc K)=RatFunc.C (v:K) := rfl
@[simp] lemma variableUnit_val : (variableUnit (K:=K):RatFunc K)=RatFunc.X := rfl
@[simp] lemma scaleAction_coefficientUnit (v w : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) (coefficientUnit w)=coefficientUnit w := by
  apply Units.ext
  simp
@[simp] lemma scaleAction_variableUnit (v : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) variableUnit=coefficientUnit v^(-2*t)*variableUnit := by
  apply Units.ext
  simp [scale_X,Units.val_zpow_eq_zpow_val,map_zpow₀]

def shearRatio (v : Kˣ) (t : ℤ) : (RatFunc K)ˣ :=
  coefficientUnit v^(t*t)*variableUnit^(-t)
@[simp] lemma shearRatio_zero (v : Kˣ) : shearRatio v 0=1 := by simp [shearRatio]
lemma shearRatio_add (v : Kˣ) (t u : ℤ) :
    shearRatio v (t+u)=shearRatio v t*scaleAction v (Multiplicative.ofAdd t) (shearRatio v u) := by
  simp only [shearRatio,map_mul,map_zpow,scaleAction_coefficientUnit,scaleAction_variableUnit,mul_zpow]
  rw [←zpow_mul,show (t+u)*(t+u)=t*t+u*u+(-2*t)*(-u) by ring,
    show -(t+u)= -t+ -u by ring,zpow_add,zpow_add,zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]
@[simp] lemma shearRatio_val (v : Kˣ) (t : ℤ) :
    (shearRatio v t:RatFunc K)=RatFunc.C (↑(v^(t*t)):K)*RatFunc.X^(-t) := by
  simp [shearRatio,Units.val_zpow_eq_zpow_val,map_zpow₀]

def reciprocalUnit : (RatFunc K)ˣ ≃* (RatFunc K)ˣ := Units.mapEquiv reciprocalEquiv.toMulEquiv
@[simp] lemma reciprocalUnit_val (a : (RatFunc K)ˣ) :
    (reciprocalUnit a:RatFunc K)=reciprocal (a:RatFunc K) := rfl
lemma reciprocalUnit_scaleAction (v : Kˣ) (t : ℤ) (a : (RatFunc K)ˣ) :
    reciprocalUnit (scaleAction v (Multiplicative.ofAdd (-t)) a)=
      scaleAction v (Multiplicative.ofAdd t) (reciprocalUnit a) := by
  apply Units.ext
  simp only [reciprocalUnit_val,scaleAction_val]
  have H:=congrArg (fun f : RatFunc K →+* RatFunc K=>f (a:RatFunc K)) (reciprocal_scale (v^(-2*(-t))))
  dsimp only [RingHom.comp_apply] at H
  rw [←zpow_neg,show -(-2*(-t))= -2*t by ring] at H
  exact H

def oppositeInverseRatio (v : Kˣ) (t : ℤ) : (RatFunc K)ˣ := reciprocalUnit (pureRatio v (-t))⁻¹
@[simp] lemma oppositeInverseRatio_zero (v : Kˣ) : oppositeInverseRatio v 0=1 := by simp [oppositeInverseRatio]
lemma oppositeInverseRatio_add (v : Kˣ) (t u : ℤ) :
    oppositeInverseRatio v (t+u)=
      oppositeInverseRatio v t*scaleAction v (Multiplicative.ofAdd t) (oppositeInverseRatio v u) := by
  simp only [oppositeInverseRatio,neg_add,pureRatio_add,map_mul,reciprocalUnit_scaleAction,
    mul_inv_rev,map_inv]
  exact mul_comm _ _
end
end ElementaryPositivity.RationalFiber

end

end OAI
