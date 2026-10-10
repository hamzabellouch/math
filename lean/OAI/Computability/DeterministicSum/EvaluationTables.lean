import Mathlib
import OAI.Computability.DeterministicSum.SparseCodes

namespace OAI

/-! Initialized evaluation grids and exact Vandermonde tables. -/

namespace DeterministicThreeSum.Structured.Indexed
open Command

lemma integerTableMemory_outside (T base i : ℕ) (xs : List ℤ) (mem : ℕ → Option ℕ) (a : ℕ)
    (ha : a<base+i ∨ base+i+xs.length≤a) : integerTableMemory T base i xs mem a=mem a := by
  induction xs generalizing i mem with
  | nil => rfl
  | cons z xs ih =>
    rw [integerTableMemory,ih (i+1) _ (by simp only [List.length_cons] at ha; omega)]
    exact Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _

lemma integerTableMemory_entry (T base i : ℕ) (xs : List ℤ) (mem : ℕ → Option ℕ)
    (j : ℕ) (hj : j<xs.length) :
    integerTableMemory T base i xs mem (base+i+j)=some (integerValue T xs[j]) := by
  induction xs generalizing i mem j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero =>
      simp only [integerTableMemory,Nat.add_zero,List.getElem_cons_zero]
      rw [integerTableMemory_outside _ _ _ _ _ _ (by omega)]
      simp
    | succ j =>
      have hj' : j<xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj
      have he : base+i+(j+1)=base+(i+1)+j := by omega
      simpa only [integerTableMemory,he,List.getElem_cons_succ] using
        ih (i+1) (Function.update mem (base+i) (some (integerValue T a))) j hj'
end DeterministicThreeSum.Structured.Indexed
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis SparseAxis DeterministicThreeSum.Rectangular Finset
open scoped BigOperators

def powerTable (T q i : ℕ) : ℕ := (i/q)^(i%q)%T

def powerIntegers (q : ℕ) : List ℤ :=
  List.ofFn (fun i : Fin (q*q) => (((i.val/q)^(i.val%q):ℕ):ℤ))

def powerTableCommand (q : ℕ) : Command := integerTable 0 (powerIntegers q)

lemma powerTable_lt {T : ℕ} (hT : 0 < T) (q i : ℕ) : powerTable T q i < T := Nat.mod_lt _ hT

lemma powerTable_entry {T q : ℕ} (hq : 0 < q) (v u : Fin q) :
    (powerTable T q (v.val*q+u.val):ZMod T)=(v.val:ZMod T)^u.val := by
  have hd : (v.val*q+u.val)/q=v.val := by
    rw [Nat.mul_comm v.val q,Nat.mul_add_div hq,Nat.div_eq_of_lt u.isLt,Nat.add_zero]
  simp [powerTable,hd,Nat.add_mod,Nat.mod_eq_of_lt u.isLt]

theorem powerTableCommand_correct {w T base q : ℕ} (s : Data)
    (hT : 0 < T) (hTw : T < wordModulus w) (hbase : base+q*q < wordModulus w)
    (hbound : ∀ i, i < q*q → (i/q)^(i%q) < wordModulus w)
    (h2 : s.registers 2=T) (h3 : s.registers 3=base) :
    ∃ cost z, Eval w (powerTableCommand q) s cost z ∧ cost ≤ 6*(q*q) ∧
      (∀ i, i < q*q → z.memory (base+i)=some (powerTable T q i)) ∧
      (∀ a, a < base ∨ base+q*q ≤ a → z.memory a=s.memory a) ∧
      (∀ r, 2 ≤ r → z.registers r=s.registers r) := by
  have hl : (powerIntegers q).length=q*q := by simp [powerIntegers]
  obtain ⟨cost,z,he,hc,hzm,hzr⟩:=integerTable_correct (i:=0) s (powerIntegers q) hT hTw
    (by simpa only [Nat.add_zero,hl] using hbase) (by
      intro a ha
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp ha
      subst a
      exact hbound i.val i.isLt) h2 h3
  refine ⟨cost,z,he,by simpa only [hl] using hc,?_,?_,hzr⟩
  · intro i hi
    rw [hzm]
    have hh:=integerTableMemory_entry T base 0 (powerIntegers q) s.memory i (by rwa [hl])
    simpa only [Nat.add_zero,powerIntegers,List.getElem_ofFn,integerValue_nat,powerTable] using hh
  · intro a ha
    rw [hzm]
    exact integerTableMemory_outside T base 0 _ _ a (by simpa only [Nat.add_zero,hl] using ha)

lemma tensorValue_evaluation {T q : ℕ} (hq : 0 < q) (d : ℕ) (x : ℕ → ℕ)
    (v : DigitBox q d) :
    (tensorValue T q q (powerTable T q) d x (lowCode q d v):ZMod T)=
      ∑ u : DigitBox q d, (x (lowCode q d u):ZMod T)*
        ∏ k : Fin d, ((digitFunction q d v k).val:ZMod T)^(digitFunction q d u k).val := by
  have he:=NewtonPass.tensorValue_low (T:=T) hq hq (powerTable T q) d 0 x v
  simp only [Nat.zero_mul,Nat.zero_add] at he
  rw [he]
  apply sum_congr rfl
  intro u _
  rw [digitCoefficient_product]
  simp_rw [powerTable_entry hq]
  rw [mul_comm]
end DeterministicThreeSum.Structured.Indexed.Cache

end OAI
