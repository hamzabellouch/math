import Mathlib
import OAI.Computability.QuantumFactoring.WordBlocks

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- A fixed-capacity little-endian word stack. No dynamic address or unbounded
list is part of the corresponding Boolean network. -/
def stackEncoding (s w : ℕ) (xs : List (Basis w)) : Basis (s*w) := fun j =>
  let ij := finProdFinEquiv.symm j
  (xs[ij.1.val]?.getD (fun _ => false)) ij.2

lemma block_stackEncoding (s w : ℕ) (xs : List (Basis w)) (i : Fin s) :
    block (stackEncoding s w xs) i = xs[i.val]?.getD (fun _ => false) := by
  funext j
  simp [block,stackEncoding]

/-- Pop the top, padding the empty end with zero. -/
def stackPop (s w : ℕ) : BooleanNetwork (s*w) (s*w) :=
  wordBlocks (fun i : Fin s => if h : i.val+1<s then blockNet s w ⟨i.val+1,h⟩
    else wordConstant 0)

/-- Push a word; the last slot is dropped. Capacity is verified separately in
controller invariants, rather than silently growing the physical width. -/
def stackPush {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    BooleanNetwork k (s*w) :=
  wordBlocks (fun i : Fin s => if h : i.val=0 then a
    else v.comp (blockNet s w ⟨i.val-1,by omega⟩))

lemma stackPop_value {s w : ℕ} (x : Basis (s*w)) (i : Fin s) :
    block ((stackPop s w).eval x) i =
      if h : i.val+1<s then block x ⟨i.val+1,h⟩ else (fun _ => false) := by
  rw [stackPop,wordBlocks_eval]
  split_ifs
  · rfl
  · funext j
    simp [wordConstant]

lemma stackPush_value {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (i : Fin s) :
    block ((stackPush a v).eval x) i =
      if _h : i.val=0 then a.eval x else block (v.eval x) ⟨i.val-1,by omega⟩ := by
  rw [stackPush,wordBlocks_eval]
  split_ifs <;> rfl

lemma block_ext {s w : ℕ} {x y : Basis (s*w)}
    (h : ∀ i : Fin s, block x i=block y i) : x=y := by
  funext j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  exact congrFun (h i) k

lemma stackPop_encoding {s w : ℕ} (xs : List (Basis w)) (h : xs.length ≤ s) :
    (stackPop s w).eval (stackEncoding s w xs)=stackEncoding s w xs.tail := by
  apply block_ext
  intro i
  rw [stackPop_value,block_stackEncoding]
  split_ifs with hi
  · rw [block_stackEncoding]
    cases xs <;> simp
  · have hh : xs.tail[i.val]?=none := by
      apply List.getElem?_eq_none
      simp only [List.length_tail]
      omega
    rw [hh]
    rfl

lemma stackPush_encoding {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (xs : List (Basis w)) (hv : v.eval x=stackEncoding s w xs) :
    (stackPush a v).eval x=stackEncoding s w (a.eval x::xs) := by
  apply block_ext
  intro i
  rw [stackPush_value,block_stackEncoding]
  split_ifs with hi
  · simp [hi]
  · rw [hv,block_stackEncoding]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp [hj]

lemma stackPop_count (s w : ℕ) : (stackPop s w).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val+1<s
  · have he : (if h : i.val+1<s then blockNet s w ⟨i.val+1,h⟩ else wordConstant 0) =
        blockNet s w ⟨i.val+1,hi⟩ := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork (s*w) w => c.net.count) he
    rw [hh,blockNet_count]
    omega
  · have he : (if h : i.val+1<s then blockNet s w ⟨i.val+1,h⟩ else wordConstant 0) =
        wordConstant 0 := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork (s*w) w => c.net.count) he
    rw [hh,wordConstant_count]

lemma stackPush_count {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    (stackPush a v).net.count ≤ s*w*(a.net.count+v.net.count) := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val=0
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=a := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh]
    omega
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=
        v.comp (blockNet s w ⟨i.val-1,by omega⟩) := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh,count_comp,blockNet_count]
    omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
