import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalCocycleExt
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalShearCocycle
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalPureAction

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
lemma oppositeInverseRatio_one_val : (oppositeInverseRatio v 1:RatFunc K)=
    1+RatFunc.C (v:K)*(RatFunc.X:RatFunc K)⁻¹ := by
  have H:=pureRatio_neg v (-1)
  change scaleAction v (Multiplicative.ofAdd (-1)) (pureRatio v 1)=(pureRatio v (-1))⁻¹ at H
  rw [pureRatio_one] at H
  change reciprocal (↑((pureRatio v (-1))⁻¹):RatFunc K)=_
  rw [←H,scaleAction_val]
  change reciprocal (scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X))=_
  simp only [map_add,map_one,map_mul,scale_constant,scale_X,
    reciprocal_constant,reciprocal_X]
  rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  norm_num
lemma cutRatio_one : shearRatio v 1*pureRatio v 1=oppositeInverseRatio v 1 := by
  apply Units.ext
  rw [Units.val_mul,shearRatio_val,pureRatio_one,oppositeInverseRatio_one_val]
  change RatFunc.C (↑(v^((1:ℤ)*1)):K)*RatFunc.X^(-(1:ℤ))*
    (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=_
  simp only [mul_one,zpow_one,zpow_neg_one,Units.val_inv_eq_inv_val,map_inv₀]
  have hx : (RatFunc.X:RatFunc K)≠0:=RatFunc.X_ne_zero
  have hv : RatFunc.C (v:K)≠0:=(map_ne_zero RatFunc.C).2 v.ne_zero
  field_simp
  ring
lemma cutRatio (t : ℤ) : shearRatio v t*pureRatio v t=oppositeInverseRatio v t := by
  have H:=cocycle_ext v (fun t=>shearRatio v t*pureRatio v t) (oppositeInverseRatio v)
    (by simp) (by simp) (by
      intro t u
      rw [shearRatio_add,pureRatio_add,map_mul]
      simp only [mul_assoc,mul_left_comm,mul_comm]) (oppositeInverseRatio_add v) (cutRatio_one v)
  exact congrFun H t

variable (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
lemma shearRatio_val_add (t u : ℤ) : (shearRatio v (t+u):RatFunc K)=
    (shearRatio v t:RatFunc K)*scale (v^(-2*t)) (shearRatio v u:RatFunc K) := by
  rw [shearRatio_add,Units.val_mul,scaleAction_val]
  rfl
lemma oppositeInverseRatio_val_add (t u : ℤ) : (oppositeInverseRatio v (t+u):RatFunc K)=
    (oppositeInverseRatio v t:RatFunc K)*scale (v^(-2*t)) (oppositeInverseRatio v u:RatFunc K) := by
  rw [oppositeInverseRatio_add,Units.val_mul,scaleAction_val]
  rfl
def shearActionHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(shearRatio v t:RatFunc K)) (by simp) (shearRatio_val_add v)
def oppositeInverseActionHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(oppositeInverseRatio v t:RatFunc K))
    (by simp) (oppositeInverseRatio_val_add v)
lemma rational_cut_identity :
    (shearActionHom v Ω α).comp (pureActionHom v Ω α)=oppositeInverseActionHom v Ω α := by
  apply RingHom.ext
  intro f
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=
    FiberTorus.gaugeAdd v Ω α _ f
  rw [FiberTorus.gauge_comp]
  have HH : (fun t=>(pureRatio v t:RatFunc K)*(shearRatio v t:RatFunc K))=
      fun t=>(oppositeInverseRatio v t:RatFunc K) := by
    funext t
    rw [mul_comm,←Units.val_mul,cutRatio]
  rw [HH]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.WallUnits
open Polynomial
noncomputable section
variable {K : Type*} [Field K]
def centeredExponent (t : ℕ) (i : Fin t) : ℤ := 2*(i:ℕ)+1-(t:ℤ)
def centeredPolynomial (v : Kˣ) (t : ℕ) : K[X] :=
  ∏i : Fin t,(1+C (↑(v^centeredExponent t i):K)*X)
lemma centeredExponent_rev (t : ℕ) (i : Fin t) :
    centeredExponent t i.rev= -centeredExponent t i := by
  simp only [centeredExponent,Fin.val_rev]
  have h:=i.isLt
  omega
lemma centeredExponent_sum (t : ℕ) : ∑i : Fin t,centeredExponent t i=0 := by
  have H : (∑i : Fin t,centeredExponent t i)=∑i : Fin t,centeredExponent t i.rev :=
    (Equiv.sum_comp (Fin.revPerm) (centeredExponent t)).symm
  simp only [centeredExponent_rev,Finset.sum_neg_distrib] at H
  omega
lemma centeredLetters_product (v : Kˣ) (t : ℕ) :
    (∏i : Fin t,(↑(v^centeredExponent t i):K))=1 := by
  have H : ∏i : Fin t,v^centeredExponent t i=v^(∑i : Fin t,centeredExponent t i) := by
    have HH (s : Finset (Fin t)) : (∏i∈s,v^centeredExponent t i)=v^(∑i∈s,centeredExponent t i) := by
      induction s using Finset.induction_on with
      | empty=>simp
      | @insert i s hi ih=>rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,zpow_add]
    exact HH Finset.univ
  have H' := congrArg (fun a : Kˣ=>(a:K)) H
  simpa only [Units.coe_prod,centeredExponent_sum,zpow_zero,Units.val_one] using H'
lemma reflect_linear (a : Kˣ) :
    (1+C (a:K)*X).reflect 1=C (a:K)*(1+C (↑(a⁻¹):K)*X) := by
  simp only [reflect_add,reflect_one,pow_one,reflect_C_mul,reflect_one_X,mul_one]
  rw [mul_add,mul_one,←mul_assoc,←map_mul,Units.mul_inv,C_1,one_mul]
  exact add_comm _ _
lemma natDegree_linear_le (a : K) : (1+C a*X).natDegree≤1 := by
  exact natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (natDegree_X_le))
lemma reflect_product_linear {J : Type*} [DecidableEq J] (s : Finset J) (a : J → K) :
    (∏i∈s,(1+C (a i)*X)).reflect s.card=∏i∈s,(1+C (a i)*X).reflect 1 := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Finset.prod_insert hi]
    have hd : (∏j∈s,(1+C (a j)*X)).natDegree≤ s.card := by
      have H0 := natDegree_prod_le s (fun j => (1+C (a j)*X))
      have H1 : (∑j∈s,(1+C (a j)*X).natDegree) ≤ ∑j∈s,(1:ℕ) :=
        Finset.sum_le_sum (fun j _ => natDegree_linear_le (a j))
      exact H0.trans (by simpa using H1)
    rw [show s.card+1=1+s.card by omega,reflect_mul _ _ (natDegree_linear_le _) hd,ih]
lemma centeredPolynomial_reflect (v : Kˣ) (t : ℕ) :
    (centeredPolynomial v t).reflect t=centeredPolynomial v t := by
  unfold centeredPolynomial
  have Hcard : t=Finset.univ.card (α:=Fin t):=by simp
  conv_lhs => arg 1; rw [Hcard]
  rw [reflect_product_linear]
  simp_rw [reflect_linear,Finset.prod_mul_distrib,←map_prod,centeredLetters_product,map_one,one_mul]
  have H : (∏i : Fin t,(1+C (↑((v^centeredExponent t i)⁻¹):K)*X))=
      ∏i : Fin t,(1+C (↑(v^centeredExponent t i.rev):K)*X) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [centeredExponent_rev,zpow_neg]
  rw [H]
  exact Equiv.prod_comp (Fin.revPerm) (fun i : Fin t=>(1+C (↑(v^centeredExponent t i):K)*X))
lemma centeredPolynomial_coeff_symmetry (v : Kˣ) (t j : ℕ) (hj : j≤t) :
    (centeredPolynomial v t).coeff j=(centeredPolynomial v t).coeff (t-j) := by
  have H:=congrArg (fun f : K[X]=>f.coeff j) (centeredPolynomial_reflect v t)
  rw [coeff_reflect,revAt_le hj] at H
  exact H.symm
end
end ElementaryPositivity.WallUnits

end

end OAI
