import Mathlib
import OAI.Computability.DeterministicSum.AxisMaps
import OAI.Computability.DeterministicSum.BilinearForms

namespace OAI

/-! Digit encodings for tensor transforms. -/

namespace DeterministicThreeSum.Structured.Indexed.Axis
open Command Finset DeterministicThreeSum.Rectangular
open scoped BigOperators

def digitCode (q : ℕ) : (d : ℕ) → DigitBox q d → ℕ
  | 0,_ => 0
  | d+1,u => u.1.val*q^d+digitCode q d u.2

lemma digitCode_lt {q : ℕ} (_hq : 0<q) (d : ℕ) (u : DigitBox q d) : digitCode q d u<q^d := by
  induction d with
  | zero => simp [digitCode]
  | succ d ih =>
    have hu:=u.1.isLt
    have ht:=ih u.2
    have hl:=Nat.mul_le_mul_right (q^d) (show u.1.val+1≤q by omega)
    simp only [digitCode,pow_succ']
    nlinarith only [hl,ht]

def digitCoefficient (T q r : ℕ) (c : ℕ → ℕ) : (d : ℕ) → DigitBox r d → DigitBox q d → ZMod T
  | 0,_,_ => 1
  | d+1,v,u => (c (v.1.val*q+u.1.val):ZMod T)*digitCoefficient T q r c d v.2 u.2

theorem tensorValue_eq_tensor {T q r : ℕ} (hq : 0<q) (hr : 0<r)
    (c : ℕ → ℕ) (d a : ℕ) (x : ℕ → ℕ) (v : DigitBox r d) :
    (tensorValue T q r c d x (a*r^d+digitCode r d v):ZMod T)=
      ∑ u : DigitBox q d, digitCoefficient T q r c d v u *
        (x (a*q^d+digitCode q d u):ZMod T) := by
  induction d generalizing a x with
  | zero => simp [tensorValue,digitCode,digitCoefficient]
  | succ d ih =>
    have hidx : a*r^(d+1)+digitCode r (d+1) v=
        (a*r+v.1.val)*r^d+digitCode r d v.2 := by
      simp only [digitCode,pow_succ']; ring
    rw [tensorValue,hidx,ih]
    simp only [digitCoefficient,digitCode,Fintype.sum_prod_type]
    calc
      (∑ u : DigitBox q d, digitCoefficient T q r c d v.2 u *
        (mapValue T q r (q^d) x c ((a*r+v.1.val)*q^d+digitCode q d u):ZMod T)) =
        ∑ u : DigitBox q d, ∑ h : Fin q, digitCoefficient T q r c d v.2 u *
          (c (v.1.val*q+h.val):ZMod T)*(x (boxIndex q (q^d) a h.val (digitCode q d u)):ZMod T) := by
            apply sum_congr rfl
            intro u _
            rw [show (a*r+v.1.val)*q^d+digitCode q d u=boxIndex r (q^d) a v.1.val (digitCode q d u) from rfl,
              mapValue_box x c hr (pow_pos hq _) v.1.isLt (digitCode_lt hq d u),mul_sum]
            apply sum_congr rfl
            intro h _
            ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro h _
        apply sum_congr rfl
        intro u _
        have he : boxIndex q (q^d) a h.val (digitCode q d u)=a*q^(d+1)+(h.val*q^d+digitCode q d u) := by
          simp only [boxIndex,pow_succ']; ring
        rw [he]
        ring

theorem tensorCommand_tensor_correct {w T q r L d A P S C : ℕ} (s : Data) (x c : ℕ → ℕ)
    (hq : 1<q) (hr : 0<r) (hA : 0<A) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hL : A*(max q r)^d≤L) (hLw : L*r+L+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+r*q<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+r*q≤P ∨ P+L≤C) (hCS : C+r*q≤S ∨ S+L≤C)
    (hregs : ∀ a : Fin 8, s.registers a.val=
      environment T (A*r*tensorStride q d) P S C (tensorStride q d) A 0 a)
    (hx : ∀ i, i<A*q^d → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → s.memory (C+i)=some (c i) ∧ c i<T) :
    ∃ cost t, Eval w (tensorCommand q r) s cost t ∧
      cost≤(((row q r).cost+5)*L+11)*d+1 ∧
      (∀ a : Fin 8, t.registers a.val=
        environment T 0 (banks d P S).1 (banks d P S).2 C 0 (A*r^d) 0 a) ∧
      (∀ (a : Fin A) (v : DigitBox r d), ∃ y,
        t.memory ((banks d P S).2+a.val*r^d+digitCode r d v)=some y ∧ y<T ∧
          (y:ZMod T)=∑ u : DigitBox q d, digitCoefficient T q r c d v u *
            (x (a.val*q^d+digitCode q d u):ZMod T)) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<S ∨ S+L≤a) → t.memory a=s.memory a) := by
  obtain ⟨cost,t,he,hcost,hregs,hm,houtside⟩:=tensorCommand_correct s x c hq hr hA hT hadd hmul hL hLw hP hS hC hPS hCP hCS hregs hx hc
  refine ⟨cost,t,he,hcost,hregs,?_,houtside⟩
  intro a v
  have hv:=digitCode_lt hr d v
  have hl:=Nat.mul_le_mul_right (r^d) (show a.val+1≤A by omega)
  have hij : a.val*r^d+digitCode r d v<A*r^d := by nlinarith only [hv,hl]
  refine ⟨_,?_,(hm _ hij).2,tensorValue_eq_tensor (by omega) hr c d a.val x v⟩
  simpa only [Nat.add_assoc] using (hm _ hij).1

end DeterministicThreeSum.Structured.Indexed.Axis

end OAI
