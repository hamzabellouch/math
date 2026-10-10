import Mathlib
import OAI.Computability.QuantumFactoring.RegisterBasis
import OAI.Computability.QuantumFactoring.BooleanOracle

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

/-- Input, output, then zero work space; this same layout is used by the
classical subroutines inside the coherent controller. -/
def packed {n m : ℕ} (r : ℕ) (x : Basis n) (y : Basis m) : Basis (n+m+r) :=
  fun i => if h : i.val < n then x ⟨i.val,h⟩
    else if h' : i.val < n+m then y ⟨i.val-n,by omega⟩ else false

lemma packed_input {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin n) :
    packed r x y ⟨i.val,by omega⟩ = x i := by simp [packed, i.isLt]

lemma packed_target {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin m) :
    packed r x y ⟨n+i.val,by omega⟩ = y i := by simp [packed, i.isLt]

lemma packed_work {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin (n+m+r))
    (hi : n+m ≤ i.val) : packed r x y i = false := by
  simp [packed, show ¬ i.val<n by omega, show ¬ i.val<n+m by omega]

def oracleIndex (n m width i : ℕ) : ℕ :=
  if i < n then i else if i < width then n+m+(i-n) else n+(i-width)

/-- Place the oracle's retained trace after its output rather than between the
input and output. A larger reservoir of work wires is permitted. -/
def oraclePlacement {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    Register (c.width+m) (n+m+r) where
  toFun i := ⟨oracleIndex n m c.width i.val, by
    have := c.net.width_eq
    have := i.isLt
    unfold oracleIndex
    split_ifs <;> omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have hh : oracleIndex n m c.width i.val = oracleIndex n m c.width j.val :=
      congrArg Fin.val he
    unfold oracleIndex at hh
    split_ifs at hh <;> have hi := i.isLt <;> have hj := j.isLt <;>
      have hn := c.net.input_le <;> omega

lemma oraclePlacement_val {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin (c.width+m)) :
    (oraclePlacement c hr i).val = oracleIndex n m c.width i.val := rfl

lemma oraclePlacement_input {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin n) :
    oraclePlacement c hr (i.castLE (c.net.input_le.trans (Nat.le_add_right _ _))) =
      ⟨i.val,by omega⟩ := by
  apply Fin.ext
  simp [oraclePlacement_val, oracleIndex, i.isLt]

lemma oraclePlacement_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin m) :
    oraclePlacement c hr ⟨c.width+i.val,by omega⟩ = ⟨n+i.val,by omega⟩ := by
  have hn := c.net.input_le
  apply Fin.ext
  simp [oraclePlacement_val, oracleIndex, show ¬c.width+i.val<n by omega]

lemma oraclePlacement_work {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin (c.width+m)) (hin : n ≤ i.val) (hiw : i.val < c.width) :
    n+m ≤ (oraclePlacement c hr i).val := by
  rw [oraclePlacement_val]
  simp only [oracleIndex, ite_eq_right (Nat.not_lt.mpr hin), ite_eq_left hiw]
  omega

def oracleOn {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    List (Instruction (n+m+r)) := c.oracle.map (Instruction.place (oraclePlacement c hr))

lemma oracleOn_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    (oracleOn c hr).length ≤ 4*c.net.count+2*m := by
  simpa [oracleOn] using oracle_length c

lemma oracleOn_basis {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (x : Basis n) (y : Basis m) :
    (programMatrix (oracleOn c hr)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r x (fun i => Bool.xor (y i) (c.eval x i))) := by
  let w := oraclePlacement c hr
  have hz : ∀ i : Fin (c.width+m), n ≤ i.val → i.val < c.width →
      (packed r x y ∘ w) i = false := by
    intro i hin hiw
    exact packed_work x y _ (oraclePlacement_work c hr i hin hiw)
  rw [oracleOn, placed_basis w c.oracle (packed r x y) _ (oracle_basis c _ hz)]
  congr 1
  have heval : (fun j : Fin n => (packed r x y ∘ w)
      (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) = x := by
    funext j
    rw [Function.comp_apply, oraclePlacement_input, packed_input]
  funext i
  by_cases hi : ∃ j, w j = i
  · obtain ⟨j,rfl⟩ := hi
    rw [Register.replace_inside]
    unfold oracleOutput
    rw [heval]
    by_cases hj : c.width ≤ j.val
    · rw [dite_eq_left hj]
      have hw : w j = (⟨n+(j.val-c.width),by have := j.isLt; omega⟩ : Fin (n+m+r)) := by
        apply Fin.ext
        simp only [w, oraclePlacement_val, oracleIndex,
          ite_eq_right (show ¬j.val<n by have := c.net.input_le; omega),
          ite_eq_right (Nat.not_lt.mpr hj)]
      change ((packed r x y) (w j) ^^ c.eval x ⟨j.val-c.width,by omega⟩) = _
      rw [hw, packed_target x y ⟨j.val-c.width,by omega⟩,
        packed_target x (fun i => y i ^^ c.eval x i) ⟨j.val-c.width,by omega⟩]
    · rw [dite_eq_right hj]
      by_cases hn : j.val < n
      · have hj' : j = (⟨j.val,hn⟩ : Fin n).castLE
          (c.net.input_le.trans (Nat.le_add_right _ _)) := rfl
        rw [hj', Function.comp_apply, oraclePlacement_input, packed_input, packed_input]
      · rw [Function.comp_apply, packed_work x y _ (oraclePlacement_work c hr j (by omega) (by omega)),
          packed_work x _ _ (oraclePlacement_work c hr j (by omega) (by omega))]
  · have hout : ∀ j, w j ≠ i := by simpa only [not_exists] using hi
    rw [Register.replace_outside w _ _ ⟨i,hout⟩]
    have hir : n+m ≤ i.val := by
      by_contra hn
      by_cases hin : i.val < n
      · exact hi ⟨(⟨i.val,hin⟩ : Fin n).castLE
          (c.net.input_le.trans (Nat.le_add_right _ _)), by
            rw [oraclePlacement_input]⟩
      · exact hi ⟨⟨c.width+(i.val-n),by omega⟩, by
          rw [oraclePlacement_target c hr ⟨i.val-n,by omega⟩]
          apply Fin.ext; dsimp; omega⟩
    rw [packed_work x y i hir, packed_work x _ i hir]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
