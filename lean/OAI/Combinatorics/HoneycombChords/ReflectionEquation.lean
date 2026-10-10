import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace OAI

/-! Polynomial matrix verification of the two-boundary reflection equation.

The specialization at a sixteenth root of minus one gives the honeycomb
reflection identity in the finite strip transfer calculation. -/
section

namespace CriticalHoneycomb.Transfer.Reflection
open scoped Matrix
abbrev Pair := Fin 3 × Fin 3
noncomputable def rNumerator (r z w : ℂ) : Matrix Pair Pair ℂ := fun p q=>
  let cc:=(r^6*w^2+r^10*z^2)*(r^4*w^2+r^12*z^2)
  let aa:=(r^4+r^12)*z*w*(r^6*w^2+r^10*z^2)
  let hh:=(r^4+r^12)*z*w*(z^2-w^2)
  let vv:=(r^6*w^2+r^10*z^2)*(z^2-w^2)
  let dd:=(z^2-w^2)*(-r^14*z^2-r^2*w^2)
  let qq:=(r^4*z^2+r^12*w^2)*(r^6*z^2+r^10*w^2)
  match p.1.val,p.2.val,q.1.val,q.2.val with
  | 0,0,0,0 => cc
  | 2,2,2,2 => cc
  | 0,1,0,1 => vv
  | 1,0,1,0 => vv
  | 2,1,2,1 => vv
  | 1,2,1,2 => vv
  | 0,1,1,0 => aa
  | 1,0,0,1 => aa
  | 2,1,1,2 => aa
  | 1,2,2,1 => aa
  | 0,2,0,2 => dd
  | 0,2,1,1 => -r^12*hh
  | 0,2,2,0 => cc-r^8*dd
  | 1,1,0,2 => r^4*hh
  | 1,1,1,1 => qq
  | 1,1,2,0 => -r^12*hh
  | 2,0,0,2 => cc+r^8*dd
  | 2,0,1,1 => r^4*hh
  | 2,0,2,0 => dd
  | _,_,_,_ => 0
noncomputable def dConstant (r z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun p q=>
  if p=q then if p=1 then z*(r^3*z^2+r^13) else z*(r^3+r^13*z^2) else 0
noncomputable def dLinear (r z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun p q=>
  if p=0 ∧ q=1 then z^4-1 else if p=1 ∧ q=2 then r^4*(z^4-1) else 0
noncomputable def slot1 (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Pair Pair ℂ :=
  fun p q=>if p.2=q.2 then M p.1 q.1 else 0
noncomputable def slot2 (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Pair Pair ℂ :=
  fun p q=>if p.1=q.1 then M p.2 q.2 else 0
noncomputable def reflectionLeft0 (r z w : ℂ) : Matrix Pair Pair ℂ :=
  rNumerator r z w * slot1 (dConstant r z) * (rNumerator r (z*w) 1)ᵀ * slot2 (dConstant r w)
noncomputable def reflectionRight0 (r z w : ℂ) : Matrix Pair Pair ℂ :=
  slot2 (dConstant r w) * (rNumerator r (z*w) 1 * slot1 (dConstant r z) * (rNumerator r z w)ᵀ)
noncomputable def reflectionLeft1 (r z w : ℂ) : Matrix Pair Pair ℂ :=
  rNumerator r z w * slot1 (dLinear r z) * (rNumerator r (z*w) 1)ᵀ * slot2 (dConstant r w)+
  rNumerator r z w * slot1 (dConstant r z) * (rNumerator r (z*w) 1)ᵀ * slot2 (dLinear r w)
noncomputable def reflectionRight1 (r z w : ℂ) : Matrix Pair Pair ℂ :=
  slot2 (dConstant r w) * (rNumerator r (z*w) 1 * slot1 (dLinear r z) * (rNumerator r z w)ᵀ)+
  slot2 (dLinear r w) * (rNumerator r (z*w) 1 * slot1 (dConstant r z) * (rNumerator r z w)ᵀ)
noncomputable def dValue (r z : ℂ) (p : Fin 3) : ℂ :=
  if p=1 then z*(r^3*z^2+r^13) else z*(r^3+r^13*z^2)
lemma mul_slot1_constant (r z : ℂ) (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (M*slot1 (dConstant r z)) p q=M p q*dValue r z q.1 := by
  classical
  simp [Matrix.mul_apply,slot1,dConstant,dValue,Fintype.sum_prod_type,mul_ite]
lemma mul_slot2_constant (r z : ℂ) (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (M*slot2 (dConstant r z)) p q=M p q*dValue r z q.2 := by
  classical
  simp [Matrix.mul_apply,slot2,dConstant,dValue,Fintype.sum_prod_type,mul_ite]
lemma slot2_constant_mul (r z : ℂ) (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (slot2 (dConstant r z)*M) p q=dValue r z p.2*M p q := by
  classical
  simp [Matrix.mul_apply,slot2,dConstant,dValue,Fintype.sum_prod_type,ite_mul]
lemma mul_slot1_linear (r z : ℂ) (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (M*slot1 (dLinear r z)) p q=
      if q.1=1 then M p (0,q.2)*(z^4-1) else
      if q.1=2 then M p (1,q.2)*(r^4*(z^4-1)) else 0 := by
  classical
  rcases q with ⟨a,b⟩
  fin_cases a <;> simp [Matrix.mul_apply,slot1,dLinear,Fintype.sum_prod_type,mul_ite]
lemma mul_slot2_linear (r z : ℂ) (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (M*slot2 (dLinear r z)) p q=
      if q.2=1 then M p (q.1,0)*(z^4-1) else
      if q.2=2 then M p (q.1,1)*(r^4*(z^4-1)) else 0 := by
  classical
  rcases q with ⟨a,b⟩
  fin_cases b <;> simp [Matrix.mul_apply,slot2,dLinear,Fintype.sum_prod_type,mul_ite]
lemma slot2_linear_mul (r z : ℂ) (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (slot2 (dLinear r z)*M) p q=
      if p.2=0 then (z^4-1)*M (p.1,1) q else
      if p.2=1 then (r^4*(z^4-1))*M (p.1,2) q else 0 := by
  classical
  rcases p with ⟨a,b⟩
  fin_cases b <;> simp [Matrix.mul_apply,slot2,dLinear,Fintype.sum_prod_type,ite_mul]
lemma core0_apply (r z : ℂ) (A B : Matrix Pair Pair ℂ) (p q : Pair) :
    (A*slot1 (dConstant r z)*Bᵀ) p q=∑ k,A p k*dValue r z k.1*B q k := by
  rw [Matrix.mul_apply]
  simp only [mul_slot1_constant,Matrix.transpose_apply]
lemma core1_apply (r z : ℂ) (A B : Matrix Pair Pair ℂ) (p q : Pair) :
    (A*slot1 (dLinear r z)*Bᵀ) p q=∑ k,
      (if k.1=1 then A p (0,k.2)*(z^4-1) else
       if k.1=2 then A p (1,k.2)*(r^4*(z^4-1)) else 0)*B q k := by
  rw [Matrix.mul_apply]
  simp only [mul_slot1_linear,Matrix.transpose_apply]
private lemma reflectionFinThreeTwo : (2:Fin 3).val=2 := rfl
private abbrev reflectionAdd (a b : ℂ) : ℂ := a+b
private abbrev reflectionMul (a b : ℂ) : ℂ := a*b
private abbrev reflectionPow (a : ℂ) (n : ℕ) : ℂ := a^n
section
variable (r z w : ℂ) (hr : r^16+1=0)
include hr
omit hr in
private lemma reflectionComponent00000 : reflectionLeft0 r z w (0,0) (0,0) = reflectionRight0 r z w (0,0) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent00001 : reflectionLeft0 r z w (0,0) (0,1) = reflectionRight0 r z w (0,0) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00002 : reflectionLeft0 r z w (0,0) (0,2) = reflectionRight0 r z w (0,0) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00010 : reflectionLeft0 r z w (0,0) (1,0) = reflectionRight0 r z w (0,0) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00011 : reflectionLeft0 r z w (0,0) (1,1) = reflectionRight0 r z w (0,0) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00012 : reflectionLeft0 r z w (0,0) (1,2) = reflectionRight0 r z w (0,0) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00020 : reflectionLeft0 r z w (0,0) (2,0) = reflectionRight0 r z w (0,0) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00021 : reflectionLeft0 r z w (0,0) (2,1) = reflectionRight0 r z w (0,0) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00022 : reflectionLeft0 r z w (0,0) (2,2) = reflectionRight0 r z w (0,0) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00100 : reflectionLeft0 r z w (0,1) (0,0) = reflectionRight0 r z w (0,1) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00101 : reflectionLeft0 r z w (0,1) (0,1) = reflectionRight0 r z w (0,1) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent00102 : reflectionLeft0 r z w (0,1) (0,2) = reflectionRight0 r z w (0,1) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00110 : reflectionLeft0 r z w (0,1) (1,0) = reflectionRight0 r z w (0,1) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent00111 : reflectionLeft0 r z w (0,1) (1,1) = reflectionRight0 r z w (0,1) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00112 : reflectionLeft0 r z w (0,1) (1,2) = reflectionRight0 r z w (0,1) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00120 : reflectionLeft0 r z w (0,1) (2,0) = reflectionRight0 r z w (0,1) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00121 : reflectionLeft0 r z w (0,1) (2,1) = reflectionRight0 r z w (0,1) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00122 : reflectionLeft0 r z w (0,1) (2,2) = reflectionRight0 r z w (0,1) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00200 : reflectionLeft0 r z w (0,2) (0,0) = reflectionRight0 r z w (0,2) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00201 : reflectionLeft0 r z w (0,2) (0,1) = reflectionRight0 r z w (0,2) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00202 : reflectionLeft0 r z w (0,2) (0,2) = reflectionRight0 r z w (0,2) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent00210 : reflectionLeft0 r z w (0,2) (1,0) = reflectionRight0 r z w (0,2) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate00211 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 56) (reflectionMul (reflectionPow z 6) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 6) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 56) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 56) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 6) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 6) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 46) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 46)) (reflectionMul (reflectionPow z 8) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 46)) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionMul (reflectionPow r 46) (reflectionMul (reflectionPow z 6) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 46) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 46)) (reflectionMul (reflectionPow z 4) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 10) (reflectionPow w 4))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 8) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 2) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 38) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 38)) (reflectionMul (reflectionPow z 8) (reflectionPow w 4))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 38)) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionMul (reflectionPow r 38) (reflectionMul (reflectionPow z 6) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 38) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 38)) (reflectionMul (reflectionPow z 4) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 34)) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionPow r 34) (reflectionMul (reflectionPow z 8) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 34) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 34)) (reflectionMul (reflectionPow z 6) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 34)) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 34) (reflectionMul (reflectionPow z 4) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 10) (reflectionPow w 4))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 26)) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionPow r 26) (reflectionMul (reflectionPow z 8) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 26) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 26)) (reflectionMul (reflectionPow z 6) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 26)) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))) (reflectionMul (reflectionPow r 26) (reflectionMul (reflectionPow z 4) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 6) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 6) (reflectionPow w 4))) (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 16)) (reflectionMul (reflectionPow z 6) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 16) (reflectionMul (reflectionPow z 6) (reflectionPow w 4))) (reflectionMul (reflectionPow r 16) (reflectionMul (reflectionPow z 4) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 16)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 16)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 16) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))))))
private lemma reflectionComponent00211 : reflectionLeft0 r z w (0,2) (1,1) = reflectionRight0 r z w (0,2) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate00211 r z w*x) hr
  dsimp only [reflectionCertificate00211,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent00212 : reflectionLeft0 r z w (0,2) (1,2) = reflectionRight0 r z w (0,2) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00220 : reflectionLeft0 r z w (0,2) (2,0) = reflectionRight0 r z w (0,2) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent00221 : reflectionLeft0 r z w (0,2) (2,1) = reflectionRight0 r z w (0,2) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent00222 : reflectionLeft0 r z w (0,2) (2,2) = reflectionRight0 r z w (0,2) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01000 : reflectionLeft0 r z w (1,0) (0,0) = reflectionRight0 r z w (1,0) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01001 : reflectionLeft0 r z w (1,0) (0,1) = reflectionRight0 r z w (1,0) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent01002 : reflectionLeft0 r z w (1,0) (0,2) = reflectionRight0 r z w (1,0) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01010 : reflectionLeft0 r z w (1,0) (1,0) = reflectionRight0 r z w (1,0) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent01011 : reflectionLeft0 r z w (1,0) (1,1) = reflectionRight0 r z w (1,0) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01012 : reflectionLeft0 r z w (1,0) (1,2) = reflectionRight0 r z w (1,0) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01020 : reflectionLeft0 r z w (1,0) (2,0) = reflectionRight0 r z w (1,0) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01021 : reflectionLeft0 r z w (1,0) (2,1) = reflectionRight0 r z w (1,0) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01022 : reflectionLeft0 r z w (1,0) (2,2) = reflectionRight0 r z w (1,0) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01100 : reflectionLeft0 r z w (1,1) (0,0) = reflectionRight0 r z w (1,1) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01101 : reflectionLeft0 r z w (1,1) (0,1) = reflectionRight0 r z w (1,1) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate01102 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 6) (reflectionPow w 8))) (reflectionMul (reflectionPow r 56) (reflectionMul (reflectionPow z 6) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 56) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionMul (reflectionPow r 56) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 56)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 6) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 6) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 46)) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionPow r 46) (reflectionMul (reflectionPow z 8) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 46) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 46)) (reflectionMul (reflectionPow z 6) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 46)) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 46) (reflectionMul (reflectionPow z 4) (reflectionPow w 4))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 38)) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionPow r 38) (reflectionMul (reflectionPow z 8) (reflectionPow w 4))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 38) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 38)) (reflectionMul (reflectionPow z 6) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 38)) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))) (reflectionMul (reflectionPow r 38) (reflectionMul (reflectionPow z 4) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 34) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 34)) (reflectionMul (reflectionPow z 8) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 34)) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 34) (reflectionMul (reflectionPow z 6) (reflectionPow w 2))) (reflectionMul (reflectionPow r 34) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 34)) (reflectionMul (reflectionPow z 4) (reflectionPow w 4))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 10) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 4) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 26) (reflectionMul (reflectionPow z 8) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 26)) (reflectionMul (reflectionPow z 8) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 26)) (reflectionMul (reflectionPow z 6) (reflectionPow w 10))) (reflectionMul (reflectionPow r 26) (reflectionMul (reflectionPow z 6) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 26) (reflectionMul (reflectionPow z 4) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 26)) (reflectionMul (reflectionPow z 4) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 6) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 6) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 2) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))) (reflectionMul (reflectionPow r 16) (reflectionMul (reflectionPow z 6) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 16)) (reflectionMul (reflectionPow z 6) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 16)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 16) (reflectionMul (reflectionPow z 4) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 16) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 16)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))))))
private lemma reflectionComponent01102 : reflectionLeft0 r z w (1,1) (0,2) = reflectionRight0 r z w (1,1) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate01102 r z w*x) hr
  dsimp only [reflectionCertificate01102,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent01110 : reflectionLeft0 r z w (1,1) (1,0) = reflectionRight0 r z w (1,1) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01111 : reflectionLeft0 r z w (1,1) (1,1) = reflectionRight0 r z w (1,1) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent01112 : reflectionLeft0 r z w (1,1) (1,2) = reflectionRight0 r z w (1,1) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate01120 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))))
private lemma reflectionComponent01120 : reflectionLeft0 r z w (1,1) (2,0) = reflectionRight0 r z w (1,1) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate01120 r z w*x) hr
  dsimp only [reflectionCertificate01120,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent01121 : reflectionLeft0 r z w (1,1) (2,1) = reflectionRight0 r z w (1,1) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01122 : reflectionLeft0 r z w (1,1) (2,2) = reflectionRight0 r z w (1,1) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01200 : reflectionLeft0 r z w (1,2) (0,0) = reflectionRight0 r z w (1,2) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01201 : reflectionLeft0 r z w (1,2) (0,1) = reflectionRight0 r z w (1,2) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01202 : reflectionLeft0 r z w (1,2) (0,2) = reflectionRight0 r z w (1,2) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01210 : reflectionLeft0 r z w (1,2) (1,0) = reflectionRight0 r z w (1,2) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01211 : reflectionLeft0 r z w (1,2) (1,1) = reflectionRight0 r z w (1,2) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01212 : reflectionLeft0 r z w (1,2) (1,2) = reflectionRight0 r z w (1,2) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent01220 : reflectionLeft0 r z w (1,2) (2,0) = reflectionRight0 r z w (1,2) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent01221 : reflectionLeft0 r z w (1,2) (2,1) = reflectionRight0 r z w (1,2) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent01222 : reflectionLeft0 r z w (1,2) (2,2) = reflectionRight0 r z w (1,2) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02000 : reflectionLeft0 r z w (2,0) (0,0) = reflectionRight0 r z w (2,0) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02001 : reflectionLeft0 r z w (2,0) (0,1) = reflectionRight0 r z w (2,0) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02002 : reflectionLeft0 r z w (2,0) (0,2) = reflectionRight0 r z w (2,0) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent02010 : reflectionLeft0 r z w (2,0) (1,0) = reflectionRight0 r z w (2,0) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate02011 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 48) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 48)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 40) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 40)) (reflectionMul (reflectionPow z 2) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 32)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 32) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 10) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 10) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 8) (reflectionPow w 10))) (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 8) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 4) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 4) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 24)) (reflectionMul (reflectionPow z 2) (reflectionPow w 8))) (reflectionMul (reflectionPow r 24) (reflectionMul (reflectionPow z 2) (reflectionPow w 4)))))))
private lemma reflectionComponent02011 : reflectionLeft0 r z w (2,0) (1,1) = reflectionRight0 r z w (2,0) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate02011 r z w*x) hr
  dsimp only [reflectionCertificate02011,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent02012 : reflectionLeft0 r z w (2,0) (1,2) = reflectionRight0 r z w (2,0) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02020 : reflectionLeft0 r z w (2,0) (2,0) = reflectionRight0 r z w (2,0) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent02021 : reflectionLeft0 r z w (2,0) (2,1) = reflectionRight0 r z w (2,0) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02022 : reflectionLeft0 r z w (2,0) (2,2) = reflectionRight0 r z w (2,0) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02100 : reflectionLeft0 r z w (2,1) (0,0) = reflectionRight0 r z w (2,1) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02101 : reflectionLeft0 r z w (2,1) (0,1) = reflectionRight0 r z w (2,1) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02102 : reflectionLeft0 r z w (2,1) (0,2) = reflectionRight0 r z w (2,1) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02110 : reflectionLeft0 r z w (2,1) (1,0) = reflectionRight0 r z w (2,1) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02111 : reflectionLeft0 r z w (2,1) (1,1) = reflectionRight0 r z w (2,1) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02112 : reflectionLeft0 r z w (2,1) (1,2) = reflectionRight0 r z w (2,1) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent02120 : reflectionLeft0 r z w (2,1) (2,0) = reflectionRight0 r z w (2,1) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02121 : reflectionLeft0 r z w (2,1) (2,1) = reflectionRight0 r z w (2,1) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent02122 : reflectionLeft0 r z w (2,1) (2,2) = reflectionRight0 r z w (2,1) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02200 : reflectionLeft0 r z w (2,2) (0,0) = reflectionRight0 r z w (2,2) (0,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02201 : reflectionLeft0 r z w (2,2) (0,1) = reflectionRight0 r z w (2,2) (0,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02202 : reflectionLeft0 r z w (2,2) (0,2) = reflectionRight0 r z w (2,2) (0,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02210 : reflectionLeft0 r z w (2,2) (1,0) = reflectionRight0 r z w (2,2) (1,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02211 : reflectionLeft0 r z w (2,2) (1,1) = reflectionRight0 r z w (2,2) (1,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02212 : reflectionLeft0 r z w (2,2) (1,2) = reflectionRight0 r z w (2,2) (1,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02220 : reflectionLeft0 r z w (2,2) (2,0) = reflectionRight0 r z w (2,2) (2,0) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02221 : reflectionLeft0 r z w (2,2) (2,1) = reflectionRight0 r z w (2,2) (2,1) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent02222 : reflectionLeft0 r z w (2,2) (2,2) = reflectionRight0 r z w (2,2) (2,2) := by
  simp only [reflectionLeft0,reflectionRight0,mul_slot2_constant,slot2_constant_mul]
  simp only [core0_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent10000 : reflectionLeft1 r z w (0,0) (0,0) = reflectionRight1 r z w (0,0) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate10001 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 11) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 12))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul ((-1:ℂ)) (reflectionMul (reflectionPow r 29) (reflectionPow z 7)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 12))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul ((-1:ℂ)) (reflectionMul (reflectionPow r 19) (reflectionPow z 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 3) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionPow r 15) (reflectionMul (z) (reflectionPow w 4))))))))
private lemma reflectionComponent10001 : reflectionLeft1 r z w (0,0) (0,1) = reflectionRight1 r z w (0,0) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate10001 r z w*x) hr
  dsimp only [reflectionCertificate10001,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent10002 : reflectionLeft1 r z w (0,0) (0,2) = reflectionRight1 r z w (0,0) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10010 : reflectionLeft1 r z w (0,0) (1,0) = reflectionRight1 r z w (0,0) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent10011 : reflectionLeft1 r z w (0,0) (1,1) = reflectionRight1 r z w (0,0) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10012 : reflectionLeft1 r z w (0,0) (1,2) = reflectionRight1 r z w (0,0) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10020 : reflectionLeft1 r z w (0,0) (2,0) = reflectionRight1 r z w (0,0) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10021 : reflectionLeft1 r z w (0,0) (2,1) = reflectionRight1 r z w (0,0) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10022 : reflectionLeft1 r z w (0,0) (2,2) = reflectionRight1 r z w (0,0) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10100 : reflectionLeft1 r z w (0,1) (0,0) = reflectionRight1 r z w (0,1) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10101 : reflectionLeft1 r z w (0,1) (0,1) = reflectionRight1 r z w (0,1) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate10102 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 49)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 49) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 49) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 49)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 49)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionPow r 49) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 11) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 9) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 7) (reflectionPow w 2)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionPow r 27) (reflectionMul (z) (reflectionPow w 8)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (z) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 3) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (z) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (z) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 11)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 11) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 11) (reflectionMul (reflectionPow z 3) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 11)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 11)) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionPow r 11) (reflectionMul (z) (reflectionPow w 4)))))))))
private lemma reflectionComponent10102 : reflectionLeft1 r z w (0,1) (0,2) = reflectionRight1 r z w (0,1) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate10102 r z w*x) hr
  dsimp only [reflectionCertificate10102,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent10110 : reflectionLeft1 r z w (0,1) (1,0) = reflectionRight1 r z w (0,1) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate10111 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionPow r 47) (reflectionMul (reflectionPow z 6) (reflectionPow w 9)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 6) (reflectionPow w 5))) (reflectionMul (reflectionPow r 47) (reflectionMul (reflectionPow z 4) (reflectionPow w 11)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionPow r 47) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 6) (reflectionPow w 9)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 6) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 8) (reflectionPow w 9)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 8) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 6) (reflectionPow w 11)))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 4) (reflectionPow w 5)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 8) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 6) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 6) (w))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 4) (reflectionPow w 7))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 8) (reflectionPow w 5))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 8) (w)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 6) (reflectionPow w 11))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 4) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 8) (reflectionPow w 7))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 6) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 6) (w))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 4) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 6) (reflectionPow w 7))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 10) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 4) (reflectionPow w 11)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 4) (reflectionPow w 11)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 2) (reflectionPow w 5)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 6) (reflectionPow w 7))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))))
private lemma reflectionComponent10111 : reflectionLeft1 r z w (0,1) (1,1) = reflectionRight1 r z w (0,1) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate10111 r z w*x) hr
  dsimp only [reflectionCertificate10111,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent10112 : reflectionLeft1 r z w (0,1) (1,2) = reflectionRight1 r z w (0,1) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate10120 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 3) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 11) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 9) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 11) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 7) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 3) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionPow r 19) (reflectionMul (z) (reflectionPow w 4))))))))
private lemma reflectionComponent10120 : reflectionLeft1 r z w (0,1) (2,0) = reflectionRight1 r z w (0,1) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate10120 r z w*x) hr
  dsimp only [reflectionCertificate10120,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent10121 : reflectionLeft1 r z w (0,1) (2,1) = reflectionRight1 r z w (0,1) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10122 : reflectionLeft1 r z w (0,1) (2,2) = reflectionRight1 r z w (0,1) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10200 : reflectionLeft1 r z w (0,2) (0,0) = reflectionRight1 r z w (0,2) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10201 : reflectionLeft1 r z w (0,2) (0,1) = reflectionRight1 r z w (0,2) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10202 : reflectionLeft1 r z w (0,2) (0,2) = reflectionRight1 r z w (0,2) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10210 : reflectionLeft1 r z w (0,2) (1,0) = reflectionRight1 r z w (0,2) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent10211 : reflectionLeft1 r z w (0,2) (1,1) = reflectionRight1 r z w (0,2) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate10212 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 6) (reflectionPow w 7)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 47) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 47) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionPow r 47) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 47)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 6) (reflectionPow w 7)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 8) (reflectionPow w 7))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 8) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 6) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 6) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 4) (reflectionPow w 7)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 8) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 6) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 4) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 4) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 8) (reflectionPow w 7))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 8) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 6) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 6) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 4) (reflectionPow w 7)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 8) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 6) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 4) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 8) (reflectionPow w 11)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 6) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 6) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 8) (w)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 4) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 6) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 6) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 2) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 10) (reflectionPow w 3))) (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 8) (reflectionPow w 9)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))))
private lemma reflectionComponent10212 : reflectionLeft1 r z w (0,2) (1,2) = reflectionRight1 r z w (0,2) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate10212 r z w*x) hr
  dsimp only [reflectionCertificate10212,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent10220 : reflectionLeft1 r z w (0,2) (2,0) = reflectionRight1 r z w (0,2) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate10221 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 11) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (z) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (z) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 5) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (z) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (z) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 3) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (z) (reflectionPow w 4))))))))
private lemma reflectionComponent10221 : reflectionLeft1 r z w (0,2) (2,1) = reflectionRight1 r z w (0,2) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate10221 r z w*x) hr
  dsimp only [reflectionCertificate10221,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent10222 : reflectionLeft1 r z w (0,2) (2,2) = reflectionRight1 r z w (0,2) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11000 : reflectionLeft1 r z w (1,0) (0,0) = reflectionRight1 r z w (1,0) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11001 : reflectionLeft1 r z w (1,0) (0,1) = reflectionRight1 r z w (1,0) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate11002 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 43) (reflectionMul (reflectionPow z 6) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 6) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 43) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 4) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 43)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 43) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 6) (reflectionPow w 7)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 4) (w)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 8) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 6) (reflectionPow w 9))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 6) (w)))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 4) (reflectionPow w 7))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 8) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 6) (reflectionPow w 11)))) (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 4) (reflectionPow w 5))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 10) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 4) (w))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 2) (reflectionPow w 7)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 8) (reflectionPow w 7))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 6) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 6) (w))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 4) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 8) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 6) (reflectionPow w 11))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 6) (reflectionPow w 3))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 4) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 6) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 6) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 2) (reflectionPow w 9)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))) (reflectionMul (reflectionPow r 13) (reflectionMul (reflectionPow z 6) (reflectionPow w 9))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 13)) (reflectionMul (reflectionPow z 6) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 13)) (reflectionMul (reflectionPow z 4) (reflectionPow w 11)))) (reflectionAdd (reflectionMul (reflectionPow r 13) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 13) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 13)) (reflectionMul (reflectionPow z 2) (reflectionPow w 5)))))))))
private lemma reflectionComponent11002 : reflectionLeft1 r z w (1,0) (0,2) = reflectionRight1 r z w (1,0) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate11002 r z w*x) hr
  dsimp only [reflectionCertificate11002,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent11010 : reflectionLeft1 r z w (1,0) (1,0) = reflectionRight1 r z w (1,0) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate11011 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 45) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 45) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 45) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (z) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionPow r 41) (reflectionMul (z) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 3) (reflectionPow w 2)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (z) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 9) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 7) (reflectionPow w 2)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 12))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionPow z 5)) (reflectionMul (reflectionPow r 29) (reflectionMul (z) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (z) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (z) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 3) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 12))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionPow z 7)) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))))))))
private lemma reflectionComponent11011 : reflectionLeft1 r z w (1,0) (1,1) = reflectionRight1 r z w (1,0) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate11011 r z w*x) hr
  dsimp only [reflectionCertificate11011,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent11012 : reflectionLeft1 r z w (1,0) (1,2) = reflectionRight1 r z w (1,0) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate11020 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 10) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 2) (reflectionPow w 5)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))
private lemma reflectionComponent11020 : reflectionLeft1 r z w (1,0) (2,0) = reflectionRight1 r z w (1,0) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate11020 r z w*x) hr
  dsimp only [reflectionCertificate11020,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent11021 : reflectionLeft1 r z w (1,0) (2,1) = reflectionRight1 r z w (1,0) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11022 : reflectionLeft1 r z w (1,0) (2,2) = reflectionRight1 r z w (1,0) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11100 : reflectionLeft1 r z w (1,1) (0,0) = reflectionRight1 r z w (1,1) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11101 : reflectionLeft1 r z w (1,1) (0,1) = reflectionRight1 r z w (1,1) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11102 : reflectionLeft1 r z w (1,1) (0,2) = reflectionRight1 r z w (1,1) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11110 : reflectionLeft1 r z w (1,1) (1,0) = reflectionRight1 r z w (1,1) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11111 : reflectionLeft1 r z w (1,1) (1,1) = reflectionRight1 r z w (1,1) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate11112 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 49) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 49)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 49)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionPow r 49) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 49) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 49)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 45) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionPow r 45) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionPow r 45) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 45) (reflectionMul (z) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 45)) (reflectionMul (z) (reflectionPow w 4))) (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 41) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 41)) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionPow r 41) (reflectionMul (z) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-3:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionMul ((3:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 5) (reflectionPow w 12))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionAdd (reflectionMul ((-1:ℂ)) (reflectionMul (reflectionPow r 33) (reflectionPow z 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (z) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (z) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 5) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (z) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (z) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (z) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 7) (reflectionPow w 12))))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul ((-1:ℂ)) (reflectionMul (reflectionPow r 23) (reflectionPow z 7)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (z) (reflectionPow w 4)))))))))
private lemma reflectionComponent11112 : reflectionLeft1 r z w (1,1) (1,2) = reflectionRight1 r z w (1,1) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate11112 r z w*x) hr
  dsimp only [reflectionCertificate11112,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent11120 : reflectionLeft1 r z w (1,1) (2,0) = reflectionRight1 r z w (1,1) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate11121 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 35)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 35) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 10) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 8) (w))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 4) (w))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 10) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 4) (reflectionPow w 3))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 2) (reflectionPow w 5))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionAdd (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 8) (w))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 4) (w))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 21)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 21) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))))))))
private lemma reflectionComponent11121 : reflectionLeft1 r z w (1,1) (2,1) = reflectionRight1 r z w (1,1) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate11121 r z w*x) hr
  dsimp only [reflectionCertificate11121,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent11122 : reflectionLeft1 r z w (1,1) (2,2) = reflectionRight1 r z w (1,1) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11200 : reflectionLeft1 r z w (1,2) (0,0) = reflectionRight1 r z w (1,2) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11201 : reflectionLeft1 r z w (1,2) (0,1) = reflectionRight1 r z w (1,2) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11202 : reflectionLeft1 r z w (1,2) (0,2) = reflectionRight1 r z w (1,2) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11210 : reflectionLeft1 r z w (1,2) (1,0) = reflectionRight1 r z w (1,2) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11211 : reflectionLeft1 r z w (1,2) (1,1) = reflectionRight1 r z w (1,2) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11212 : reflectionLeft1 r z w (1,2) (1,2) = reflectionRight1 r z w (1,2) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11220 : reflectionLeft1 r z w (1,2) (2,0) = reflectionRight1 r z w (1,2) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11221 : reflectionLeft1 r z w (1,2) (2,1) = reflectionRight1 r z w (1,2) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent11222 : reflectionLeft1 r z w (1,2) (2,2) = reflectionRight1 r z w (1,2) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  all_goals ring

omit hr in
private lemma reflectionComponent12000 : reflectionLeft1 r z w (2,0) (0,0) = reflectionRight1 r z w (2,0) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12001 : reflectionLeft1 r z w (2,0) (0,1) = reflectionRight1 r z w (2,0) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12002 : reflectionLeft1 r z w (2,0) (0,2) = reflectionRight1 r z w (2,0) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12010 : reflectionLeft1 r z w (2,0) (1,0) = reflectionRight1 r z w (2,0) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12011 : reflectionLeft1 r z w (2,0) (1,1) = reflectionRight1 r z w (2,0) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate12012 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 39)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 39) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 31)) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionPow r 31) (reflectionMul (reflectionPow z 2) (reflectionPow w 3))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 10) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 10) (reflectionPow w 5)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 8) (reflectionPow w 11))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 8) (reflectionPow w 3))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 4) (reflectionPow w 11))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 4) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 2) (reflectionPow w 9))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 2) (reflectionPow w 5)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 10) (reflectionPow w 7))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 10) (reflectionPow w 3)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 8) (reflectionPow w 9))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 8) (w))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 4) (reflectionPow w 9))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 4) (w)))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 2) (reflectionPow w 7))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 2) (reflectionPow w 3)))))))
private lemma reflectionComponent12012 : reflectionLeft1 r z w (2,0) (1,2) = reflectionRight1 r z w (2,0) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate12012 r z w*x) hr
  dsimp only [reflectionCertificate12012,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent12020 : reflectionLeft1 r z w (2,0) (2,0) = reflectionRight1 r z w (2,0) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate12021 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 3) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 9) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 9) (reflectionPow w 2)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))) (reflectionMul (reflectionPow r 25) (reflectionMul (reflectionPow z 7) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-2:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((2:ℂ)) (reflectionPow r 25)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionPow r 23) (reflectionMul (z) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (z) (reflectionPow w 4))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 9) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 17) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 17)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 5) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 15) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2)))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 15)) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionPow r 15) (reflectionMul (z) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionPow r 7) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 7)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 7)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionMul (reflectionPow r 7) (reflectionMul (reflectionPow z 3) (reflectionPow w 2)))) (reflectionAdd (reflectionMul (reflectionPow r 7) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 7)) (reflectionMul (z) (reflectionPow w 4))))))))
private lemma reflectionComponent12021 : reflectionLeft1 r z w (2,0) (2,1) = reflectionRight1 r z w (2,0) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate12021 r z w*x) hr
  dsimp only [reflectionCertificate12021,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent12022 : reflectionLeft1 r z w (2,0) (2,2) = reflectionRight1 r z w (2,0) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12100 : reflectionLeft1 r z w (2,1) (0,0) = reflectionRight1 r z w (2,1) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12101 : reflectionLeft1 r z w (2,1) (0,1) = reflectionRight1 r z w (2,1) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12102 : reflectionLeft1 r z w (2,1) (0,2) = reflectionRight1 r z w (2,1) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12110 : reflectionLeft1 r z w (2,1) (1,0) = reflectionRight1 r z w (2,1) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12111 : reflectionLeft1 r z w (2,1) (1,1) = reflectionRight1 r z w (2,1) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12112 : reflectionLeft1 r z w (2,1) (1,2) = reflectionRight1 r z w (2,1) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12120 : reflectionLeft1 r z w (2,1) (2,0) = reflectionRight1 r z w (2,1) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12121 : reflectionLeft1 r z w (2,1) (2,1) = reflectionRight1 r z w (2,1) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

private noncomputable def reflectionCertificate12122 (r z w : ℂ) : ℂ :=
  reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 11) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 11) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 9) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionMul (reflectionPow r 37) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 37)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 9) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 9) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 12))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 7) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionPow r 33) (reflectionPow z 7))) (reflectionAdd (reflectionMul (reflectionPow r 33) (reflectionMul (reflectionPow z 5) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 33)) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 7) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 7) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 5) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 5) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 29) (reflectionMul (reflectionPow z 3) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 29)) (reflectionMul (reflectionPow z 3) (reflectionPow w 4)))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 9) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 9) (reflectionPow w 4)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 7) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionMul (reflectionPow r 27) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 27)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 7) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 7) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 12))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 5) (reflectionPow w 8))))))) (reflectionAdd (reflectionAdd (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionPow r 23) (reflectionPow z 5))) (reflectionAdd (reflectionMul (reflectionPow r 23) (reflectionMul (reflectionPow z 3) (reflectionPow w 10))) (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 23)) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 5) (reflectionPow w 8)))))) (reflectionAdd (reflectionAdd (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 5) (reflectionPow w 4))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (reflectionPow z 3) (reflectionPow w 10)))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (reflectionPow z 3) (reflectionPow w 2))) (reflectionAdd (reflectionMul (reflectionPow r 19) (reflectionMul (z) (reflectionPow w 8))) (reflectionMul (reflectionMul ((-1:ℂ)) (reflectionPow r 19)) (reflectionMul (z) (reflectionPow w 4))))))))
private lemma reflectionComponent12122 : reflectionLeft1 r z w (2,1) (2,2) = reflectionRight1 r z w (2,1) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]
  have hq:=congrArg (fun x : ℂ=>reflectionCertificate12122 r z w*x) hr
  dsimp only [reflectionCertificate12122,reflectionAdd,reflectionMul,reflectionPow] at hq
  linear_combination hq

omit hr in
private lemma reflectionComponent12200 : reflectionLeft1 r z w (2,2) (0,0) = reflectionRight1 r z w (2,2) (0,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [dValue,rNumerator]

omit hr in
private lemma reflectionComponent12201 : reflectionLeft1 r z w (2,2) (0,1) = reflectionRight1 r z w (2,2) (0,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12202 : reflectionLeft1 r z w (2,2) (0,2) = reflectionRight1 r z w (2,2) (0,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12210 : reflectionLeft1 r z w (2,2) (1,0) = reflectionRight1 r z w (2,2) (1,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [dValue,rNumerator]

omit hr in
private lemma reflectionComponent12211 : reflectionLeft1 r z w (2,2) (1,1) = reflectionRight1 r z w (2,2) (1,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12212 : reflectionLeft1 r z w (2,2) (1,2) = reflectionRight1 r z w (2,2) (1,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12220 : reflectionLeft1 r z w (2,2) (2,0) = reflectionRight1 r z w (2,2) (2,0) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [dValue,rNumerator]

omit hr in
private lemma reflectionComponent12221 : reflectionLeft1 r z w (2,2) (2,1) = reflectionRight1 r z w (2,2) (2,1) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

omit hr in
private lemma reflectionComponent12222 : reflectionLeft1 r z w (2,2) (2,2) = reflectionRight1 r z w (2,2) (2,2) := by
  simp only [reflectionLeft1,reflectionRight1,Matrix.add_apply,mul_slot2_constant,slot2_constant_mul,mul_slot2_linear,slot2_linear_mul]
  simp only [core0_apply,core1_apply]
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,dValue,rNumerator]

theorem reflection_constant : reflectionLeft0 r z w=reflectionRight0 r z w := by
  funext p q
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact reflectionComponent00000 r z w
  · exact reflectionComponent00001 r z w
  · exact reflectionComponent00002 r z w
  · exact reflectionComponent00010 r z w
  · exact reflectionComponent00011 r z w
  · exact reflectionComponent00012 r z w
  · exact reflectionComponent00020 r z w
  · exact reflectionComponent00021 r z w
  · exact reflectionComponent00022 r z w
  · exact reflectionComponent00100 r z w
  · exact reflectionComponent00101 r z w
  · exact reflectionComponent00102 r z w
  · exact reflectionComponent00110 r z w
  · exact reflectionComponent00111 r z w
  · exact reflectionComponent00112 r z w
  · exact reflectionComponent00120 r z w
  · exact reflectionComponent00121 r z w
  · exact reflectionComponent00122 r z w
  · exact reflectionComponent00200 r z w
  · exact reflectionComponent00201 r z w
  · exact reflectionComponent00202 r z w
  · exact reflectionComponent00210 r z w
  · exact reflectionComponent00211 r z w hr
  · exact reflectionComponent00212 r z w
  · exact reflectionComponent00220 r z w
  · exact reflectionComponent00221 r z w
  · exact reflectionComponent00222 r z w
  · exact reflectionComponent01000 r z w
  · exact reflectionComponent01001 r z w
  · exact reflectionComponent01002 r z w
  · exact reflectionComponent01010 r z w
  · exact reflectionComponent01011 r z w
  · exact reflectionComponent01012 r z w
  · exact reflectionComponent01020 r z w
  · exact reflectionComponent01021 r z w
  · exact reflectionComponent01022 r z w
  · exact reflectionComponent01100 r z w
  · exact reflectionComponent01101 r z w
  · exact reflectionComponent01102 r z w hr
  · exact reflectionComponent01110 r z w
  · exact reflectionComponent01111 r z w
  · exact reflectionComponent01112 r z w
  · exact reflectionComponent01120 r z w hr
  · exact reflectionComponent01121 r z w
  · exact reflectionComponent01122 r z w
  · exact reflectionComponent01200 r z w
  · exact reflectionComponent01201 r z w
  · exact reflectionComponent01202 r z w
  · exact reflectionComponent01210 r z w
  · exact reflectionComponent01211 r z w
  · exact reflectionComponent01212 r z w
  · exact reflectionComponent01220 r z w
  · exact reflectionComponent01221 r z w
  · exact reflectionComponent01222 r z w
  · exact reflectionComponent02000 r z w
  · exact reflectionComponent02001 r z w
  · exact reflectionComponent02002 r z w
  · exact reflectionComponent02010 r z w
  · exact reflectionComponent02011 r z w hr
  · exact reflectionComponent02012 r z w
  · exact reflectionComponent02020 r z w
  · exact reflectionComponent02021 r z w
  · exact reflectionComponent02022 r z w
  · exact reflectionComponent02100 r z w
  · exact reflectionComponent02101 r z w
  · exact reflectionComponent02102 r z w
  · exact reflectionComponent02110 r z w
  · exact reflectionComponent02111 r z w
  · exact reflectionComponent02112 r z w
  · exact reflectionComponent02120 r z w
  · exact reflectionComponent02121 r z w
  · exact reflectionComponent02122 r z w
  · exact reflectionComponent02200 r z w
  · exact reflectionComponent02201 r z w
  · exact reflectionComponent02202 r z w
  · exact reflectionComponent02210 r z w
  · exact reflectionComponent02211 r z w
  · exact reflectionComponent02212 r z w
  · exact reflectionComponent02220 r z w
  · exact reflectionComponent02221 r z w
  · exact reflectionComponent02222 r z w
theorem reflection_linear : reflectionLeft1 r z w=reflectionRight1 r z w := by
  funext p q
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact reflectionComponent10000 r z w
  · exact reflectionComponent10001 r z w hr
  · exact reflectionComponent10002 r z w
  · exact reflectionComponent10010 r z w
  · exact reflectionComponent10011 r z w
  · exact reflectionComponent10012 r z w
  · exact reflectionComponent10020 r z w
  · exact reflectionComponent10021 r z w
  · exact reflectionComponent10022 r z w
  · exact reflectionComponent10100 r z w
  · exact reflectionComponent10101 r z w
  · exact reflectionComponent10102 r z w hr
  · exact reflectionComponent10110 r z w
  · exact reflectionComponent10111 r z w hr
  · exact reflectionComponent10112 r z w
  · exact reflectionComponent10120 r z w hr
  · exact reflectionComponent10121 r z w
  · exact reflectionComponent10122 r z w
  · exact reflectionComponent10200 r z w
  · exact reflectionComponent10201 r z w
  · exact reflectionComponent10202 r z w
  · exact reflectionComponent10210 r z w
  · exact reflectionComponent10211 r z w
  · exact reflectionComponent10212 r z w hr
  · exact reflectionComponent10220 r z w
  · exact reflectionComponent10221 r z w hr
  · exact reflectionComponent10222 r z w
  · exact reflectionComponent11000 r z w
  · exact reflectionComponent11001 r z w
  · exact reflectionComponent11002 r z w hr
  · exact reflectionComponent11010 r z w
  · exact reflectionComponent11011 r z w hr
  · exact reflectionComponent11012 r z w
  · exact reflectionComponent11020 r z w hr
  · exact reflectionComponent11021 r z w
  · exact reflectionComponent11022 r z w
  · exact reflectionComponent11100 r z w
  · exact reflectionComponent11101 r z w
  · exact reflectionComponent11102 r z w
  · exact reflectionComponent11110 r z w
  · exact reflectionComponent11111 r z w
  · exact reflectionComponent11112 r z w hr
  · exact reflectionComponent11120 r z w
  · exact reflectionComponent11121 r z w hr
  · exact reflectionComponent11122 r z w
  · exact reflectionComponent11200 r z w
  · exact reflectionComponent11201 r z w
  · exact reflectionComponent11202 r z w
  · exact reflectionComponent11210 r z w
  · exact reflectionComponent11211 r z w
  · exact reflectionComponent11212 r z w
  · exact reflectionComponent11220 r z w
  · exact reflectionComponent11221 r z w
  · exact reflectionComponent11222 r z w
  · exact reflectionComponent12000 r z w
  · exact reflectionComponent12001 r z w
  · exact reflectionComponent12002 r z w
  · exact reflectionComponent12010 r z w
  · exact reflectionComponent12011 r z w
  · exact reflectionComponent12012 r z w hr
  · exact reflectionComponent12020 r z w
  · exact reflectionComponent12021 r z w hr
  · exact reflectionComponent12022 r z w
  · exact reflectionComponent12100 r z w
  · exact reflectionComponent12101 r z w
  · exact reflectionComponent12102 r z w
  · exact reflectionComponent12110 r z w
  · exact reflectionComponent12111 r z w
  · exact reflectionComponent12112 r z w
  · exact reflectionComponent12120 r z w
  · exact reflectionComponent12121 r z w
  · exact reflectionComponent12122 r z w hr
  · exact reflectionComponent12200 r z w
  · exact reflectionComponent12201 r z w
  · exact reflectionComponent12202 r z w
  · exact reflectionComponent12210 r z w
  · exact reflectionComponent12211 r z w
  · exact reflectionComponent12212 r z w
  · exact reflectionComponent12220 r z w
  · exact reflectionComponent12221 r z w
  · exact reflectionComponent12222 r z w
end
end CriticalHoneycomb.Transfer.Reflection

end

end OAI
