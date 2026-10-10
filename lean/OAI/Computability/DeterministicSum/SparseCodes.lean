import Mathlib
import OAI.Computability.DeterministicSum.NewtonTables

namespace OAI

/-! Sparse digit coding and low-degree transform identification. -/

namespace DeterministicThreeSum.Structured.Indexed.SparseAxis
open DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators
def lowCode (q : ℕ) : (d : ℕ) → DigitBox q d → ℕ
  | 0,_ => 0
  | d+1,u => u.1.val+q*lowCode q d u.2

lemma lowCode_lt {q : ℕ} (_hq : 0 < q) (d : ℕ) (u : DigitBox q d) : lowCode q d u<q^d := by
  induction d with
  | zero => simp [lowCode]
  | succ d ih =>
    have hh:=Nat.mul_le_mul_left q (show lowCode q d u.2+1≤q^d by have h:=ih u.2; omega)
    have hu:=u.1.isLt
    simp only [lowCode,pow_succ']
    nlinarith only [hh,hu]

end DeterministicThreeSum.Structured.Indexed.SparseAxis

namespace DeterministicThreeSum.Structured.Indexed.SparseAxis
open DeterministicThreeSum.Rectangular Axis Finset
open scoped BigOperators
noncomputable section
lemma lowCode_sum (q d : ℕ) (u : DigitBox q d) :
    lowCode q d u=∑ k : Fin d, (digitFunction q d u k).val*q^k.val := by
  induction d with
  | zero => simp [lowCode]
  | succ d ih =>
    simp only [lowCode,ih,Fin.sum_univ_succ,digitFunction,Fin.cons_zero,Fin.cons_succ,
      Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro k _
    ring
lemma digitCode_sum (q d : ℕ) (u : DigitBox q d) :
    digitCode q d u=∑ k : Fin d, (digitFunction q d u k).val*q^(d-1-k.val) := by
  induction d with
  | zero => simp [digitCode]
  | succ d ih =>
    simp only [digitCode,ih,Fin.sum_univ_succ,digitFunction,Fin.cons_zero,Fin.cons_succ,
      Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero,Fin.val_succ]
    congr 1
    apply sum_congr rfl
    intro k _
    congr 2
    omega

def reverseDigit (q d : ℕ) (u : DigitBox q d) : DigitBox q d :=
  functionDigit q d (fun i => digitFunction q d u i.rev)
lemma digitFunction_reverse (q d : ℕ) (u : DigitBox q d) (i : Fin d) :
    digitFunction q d (reverseDigit q d u) i=digitFunction q d u i.rev := by
  simp [reverseDigit,digitFunction_functionDigit]
lemma reverseDigit_twice (q d : ℕ) (u : DigitBox q d) :
    reverseDigit q d (reverseDigit q d u)=u := by
  apply (digitFunctionEquiv q d).injective
  funext i
  change digitFunction q d _ i=digitFunction q d u i
  simp only [digitFunction_reverse,Fin.rev_rev]
def reverseEquiv (q d : ℕ) : Equiv.Perm (DigitBox q d) :=
  Function.Involutive.toPerm (reverseDigit q d) (reverseDigit_twice q d)
lemma digitCode_reverse (q d : ℕ) (u : DigitBox q d) :
    digitCode q d (reverseDigit q d u)=lowCode q d u := by
  rw [digitCode_sum,lowCode_sum]
  simp only [digitFunction_reverse]
  rw [← Equiv.sum_comp (Fin.revPerm : Fin d ≃ Fin d)]
  apply sum_congr rfl
  intro i _
  simp only [Fin.revPerm_apply,Fin.rev_rev]
  congr 2
  have hi:=i.isLt
  rw [Fin.val_rev]
  omega
lemma lowCode_reverse (q d : ℕ) (u : DigitBox q d) :
    lowCode q d (reverseDigit q d u)=digitCode q d u := by
  rw [← digitCode_reverse,reverseDigit_twice]
lemma digitCoefficient_reverse (T q r : ℕ) (c : ℕ → ℕ) (d : ℕ)
    (v : DigitBox r d) (u : DigitBox q d) :
    digitCoefficient T q r c d (reverseDigit r d v) (reverseDigit q d u)=
      digitCoefficient T q r c d v u := by
  simp only [digitCoefficient_product,digitFunction_reverse]
  exact Equiv.prod_comp (Fin.revPerm : Fin d ≃ Fin d) (fun k : Fin d => (c ((digitFunction r d v k).val*q+(digitFunction q d u k).val):ZMod T))
end
end DeterministicThreeSum.Structured.Indexed.SparseAxis

namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis SparseAxis DeterministicThreeSum.Newton DeterministicThreeSum.Rectangular Finset
open scoped BigOperators
noncomputable section
lemma tensorValue_low {T q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (c : ℕ → ℕ) (d a : ℕ) (x : ℕ → ℕ) (v : DigitBox r d) :
    (tensorValue T q r c d x (a*r^d+lowCode r d v):ZMod T)=
      ∑ u : DigitBox q d, digitCoefficient T q r c d v u *
        (x (a*q^d+lowCode q d u):ZMod T) := by
  rw [← digitCode_reverse r d v,tensorValue_eq_tensor hq hr]
  rw [← Equiv.sum_comp (reverseEquiv q d)]
  apply sum_congr rfl
  intro u _
  change digitCoefficient T q r c d (reverseDigit r d v) (reverseDigit q d u)*
    (x (a*q^d+digitCode q d (reverseDigit q d u)):ZMod T)=_
  rw [digitCoefficient_reverse,digitCode_reverse]
lemma lowCode_degree {q : ℕ} (hq : 0 < q) (d : ℕ) (u : DigitBox q d) :
    DigitSum.value q d (lowCode q d u)=degree (digitFunction q d u) := by
  rw [← digitCode_reverse q d u,digitCode_degree hq]
  simp only [degree,digitFunction_reverse]
  exact Equiv.sum_comp (Fin.revPerm : Fin d ≃ Fin d) (fun i => (digitFunction q d u i).val)
lemma tensorValue_coefficients_low {T q d : ℕ} (hT : 0<T) (hq : 0<q)
    (node : Fin q → ZMod T) (x : ℕ → ℕ) (a : ℕ) (v : DigitBox q d) :
    (tensorValue T q q (inverseTable T q node) d x (a*q^d+lowCode q d v):ZMod T)=
      coefficients node (fun u => (x (a*q^d+lowCode q d (functionDigit q d u)):ZMod T))
        (digitFunction q d v) := by
  rw [tensorValue_low hq hq]
  unfold coefficients Matrix.mulVec dotProduct tensor
  rw [← (digitFunctionEquiv q d).sum_comp]
  apply sum_congr rfl
  intro u _
  simp only [digitCoefficient_product,inverseTable_entry hT,
    digitFunctionEquiv,Equiv.coe_fn_mk,functionDigit_digitFunction]

theorem output_source_low {T q d D : ℕ} (hT : 0<T) (hq : 0<q)
    (node : Fin q → ZMod T) (x : ℕ → ℕ) (a : ℕ) (v : DigitBox q d) :
    (tensorValue T q q (conversionTable T q node) d
      (filtered q d D (tensorValue T q q (inverseTable T q node) d x))
      (a*q^d+lowCode q d v):ZMod T)=
    (truncatedPolynomial node
      (fun u => (x (a*q^d+lowCode q d (functionDigit q d u)):ZMod T)) D).coeff
      (exponentVector (digitFunction q d v)) := by
  rw [tensorValue_low hq hq,coefficient_truncated]
  rw [← (digitFunctionEquiv q d).sum_comp]
  apply sum_congr rfl
  intro u _
  have hm : (a*q^d+lowCode q d u)%(q^d)=lowCode q d u := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt (lowCode_lt hq d u)]
  change digitCoefficient T q q (conversionTable T q node) d v u *
      (filtered q d D (tensorValue T q q (inverseTable T q node) d x)
        (a*q^d+lowCode q d u):ZMod T) =
    (if degree (digitFunction q d u)≤D then
      coefficients node (fun u => (x (a*q^d+lowCode q d (functionDigit q d u)):ZMod T))
        (digitFunction q d u) else 0) *
      ∏ i, conversion node (digitFunction q d u i) (digitFunction q d v i)
  simp only [digitCoefficient_product,conversionTable_entry hT,filtered,hm,lowCode_degree hq]
  by_cases hh : degree (digitFunction q d u)≤D
  · simp only [not_lt.mpr hh,ite_false,hh,ite_true,tensorValue_coefficients_low hT hq]
    ring
  · simp [hh,show D<degree (digitFunction q d u) by omega]

end
end DeterministicThreeSum.Structured.Indexed.NewtonPass

namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis SparseAxis DeterministicThreeSum.Newton
noncomputable section
theorem paidCommand_source_low {w p e q L d A P S C E D k : ℕ}
    (order : Equiv.Perm (Fin q)) (s : Data) (x : ℕ → ℕ)
    (hk : 16≤k) (hkw : (tensorCommand q q).writes.sup id<k)
    (hp : p.Prime) (hq : 1<q) (hqp : q<p) (hA : 0<A)
    (hadd : 2*(p^(e+1))<wordModulus w) (hmul : (p^(e+1))*(p^(e+1))<wordModulus w)
    (hL : A*q^d≤L) (hLw : L*q+L+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+q*q<wordModulus w) (hE : E+q*q<wordModulus w) (hD : D<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+q*q≤P ∨ P+L≤C) (hCS : C+q*q≤S ∨ S+L≤C)
    (hEP : E+q*q≤P ∨ P+L≤E) (hES : E+q*q≤S ∨ S+L≤E)
    (hCE : E+q*q≤C ∨ C+q*q≤E)
    (hden : inverseDenominator order<wordModulus w)
    (hints : ∀ a∈NewtonTable.numerators order, a.natAbs<wordModulus w)
    (hconv : ∀ a∈NewtonConversionTable.integers order, a.natAbs<wordModulus w)
    (hctx : ∀ i, i<8 → s.registers (k+i)=context A (tensorStride q d) (A*q*tensorStride q d) (q^d) D E (p^(e+1)) i)
    (h10 : s.registers (k+10)=P) (h11 : s.registers (k+11)=S) (h12 : s.registers (k+12)=C)
    (hx : ∀ i, i<A*q^d → s.memory (S+i)=some (x i) ∧ x i<p^(e+1)) :
    ∃ cost z, Eval w (paidCommand p k order) s cost z ∧
      cost≤2*(((row q q).cost+5)*L+11)*d+(5*d+10)*(A*q^d)+20*w+18*(q*q)+61 ∧
      (∀ a : Fin 8, z.registers a.val=environment (p^(e+1)) 0 P S E 0 (A*q^d) 0 a) ∧
      (∀ (a : Fin A) (v : DeterministicThreeSum.Rectangular.DigitBox q d), ∃ y,
        z.memory (S+a.val*q^d+lowCode q d v)=some y ∧
        (y:ZMod (p^(e+1)))=
          (truncatedPolynomial (fun j => ((order j).val:ZMod (p^(e+1))))
            (fun u => (x (a.val*q^d+lowCode q d (SparseAxis.functionDigit q d u)):ZMod (p^(e+1)))) D).coeff
              (exponentVector (SparseAxis.digitFunction q d v))) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<S ∨ S+L≤a) →
        (a<C ∨ C+q*q≤a) → (a<E ∨ E+q*q≤a) → z.memory a=s.memory a) := by
  obtain ⟨cost,z,hz,hcost,hregs,hm,hframe⟩:=paidCommand_correct order s x hk hkw hp hq hqp hA
    hadd hmul hL hLw hP hS hC hE hD hPS hCP hCS hEP hES hCE hden hints hconv hctx h10 h11 h12 hx
  refine ⟨cost,z,hz,hcost,hregs,?_,hframe⟩
  intro a v
  have hv:=lowCode_lt (by omega : 0<q) d v
  have ha:=Nat.mul_le_mul_right (q^d) (show a.val+1≤A by omega)
  have hi : a.val*q^d+lowCode q d v<A*q^d := by nlinarith only [ha,hv]
  refine ⟨_,?_,output_source_low (pow_pos hp.pos _) (by omega) _ x a.val v⟩
  simpa only [Nat.add_assoc] using hm _ hi
end
end DeterministicThreeSum.Structured.Indexed.NewtonPass

end OAI
