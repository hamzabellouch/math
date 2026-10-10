import OAI.Computability.MatchingCount.RawBitsBridge

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α : Type} [Coding α] [Inhabited α]
@[fun_prop] theorem listReverse : Poly (List.reverse : List α → List α) := by
  have hf := listFoldAdd (fun z : List α×α => z.2::z.1) (by fun_prop) 1 (by
    intro z
    simp only [code_cons,pairBits_length]
    omega)
  have hh := comp _ (fun l : List α => (l,([]:List α))) hf (by fun_prop)
  exact hh.congr (fun l => by simp)
@[fun_prop] theorem listTake : Poly (fun z : ℕ×List α => z.2.take z.1) := by
  have hh : Poly (fun z : ℕ×List α => (z.2.reverse.drop (z.2.length-z.1)).reverse) := by fun_prop
  exact hh.congr (fun z => by rw [←List.reverse_take,List.reverse_reverse])
end Poly
end BinaryMatching.StackCode

namespace BinaryMatching.Parse
open StackCode Polynomial

def zeroPrefix (l : List Bool) : ℕ := l.foldr (fun b k => if b then 0 else k+1) 0
lemma zeroPrefix_delimited (k : ℕ) (l : List Bool) : zeroPrefix (List.replicate k false++true::l)=k := by
  induction k with
  | zero => simp [zeroPrefix]
  | succ k ih =>
    change zeroPrefix (false::(List.replicate k false++true::l))=k+1
    change zeroPrefix (List.replicate k false++true::l)+1=k+1
    rw [ih]
lemma zeroPrefix_le (l : List Bool) : zeroPrefix l≤l.length := by
  induction l with
  | nil => simp [zeroPrefix]
  | cons b l ih => cases b <;> simp_all [zeroPrefix]

@[fun_prop] theorem zeroPrefix_poly : Poly zeroPrefix := by
  have hf := Poly.listFoldAdd (fun z : ℕ×Bool => if z.2 then 0 else z.1+1) (by fun_prop) 1 (by
    intro z
    cases z.2 <;> simp)
  have hh := Poly.comp _ (fun l : List Bool => (l.reverse,0)) hf (by fun_prop)
  exact hh.congr (fun _ => by simp [zeroPrefix])

def numeral (l : List Bool) : List Bool×List Bool :=
  let k := zeroPrefix l
  ((l.drop (k+1)).take k,l.drop (2*k+1))
lemma numeral_encode (n : ℕ) (l : List Bool) : numeral (encodeNat n++l)=(n.bits,l) := by
  unfold numeral encodeNat
  rw [List.append_assoc,List.cons_append,zeroPrefix_delimited]
  simp [List.drop_append,List.drop_replicate]
  rw [show n.bits.length-(2*n.bits.length+1)=0 by omega,
    show 2*n.bits.length+1-n.bits.length=n.bits.length+1 by omega]
  simp
lemma numeral_nil : numeral []=([],[]) := rfl
lemma numeral_lengths (l : List Bool) : (numeral l).1.length≤l.length ∧ (numeral l).2.length≤l.length := by
  simp only [numeral,List.length_take,List.length_drop]
  omega
@[fun_prop] theorem numeral_poly : Poly numeral := by unfold numeral; fun_prop

def value (l : List Bool) : ℕ := l.foldr Nat.bit 0
lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih => simpa only [Nat.bits_append_bit n b h,value,List.foldr_cons] using congrArg (Nat.bit b) ih

def capStep (z : (ℕ×ℕ)×Bool) : ℕ×ℕ := (z.1.1,min z.1.1 (2*z.1.2+if z.2 then 1 else 0))
lemma capStep_fold (b : ℕ) (l : List Bool) (a : ℕ) :
    l.foldr (fun c z => capStep (z,c)) (b,min b a)=(b,min b (l.foldr Nat.bit a)) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldr_cons,ih]
    apply Prod.ext
    · rfl
    · cases c <;> simp [capStep,List.foldr_cons,Nat.bit] <;> omega

def boundedValue (b : ℕ) (l : List Bool) : ℕ := (l.reverse.foldl (fun z c => capStep (z,c)) (b,0)).2
lemma boundedValue_eq (b : ℕ) (l : List Bool) : boundedValue b l=min b (value l) := by
  unfold boundedValue
  rw [List.foldl_reverse,show (b,0)=(b,min b 0) by simp,capStep_fold]
  rfl
lemma boundedValue_bits (b n : ℕ) : boundedValue b n.bits=min b n := by rw [boundedValue_eq,value_bits]
lemma capStep_fold_bound (l : List Bool) (z : ℕ×ℕ) :
    (l.foldl (fun z c => capStep (z,c)) z).1=z.1 ∧
    (l.foldl (fun z c => capStep (z,c)) z).2≤ max z.1 z.2 := by
  induction l generalizing z with
  | nil => exact ⟨rfl,Nat.le_max_right _ _⟩
  | cons c l ih =>
    obtain ⟨h₁,h₂⟩ := ih (capStep (z,c))
    refine ⟨h₁,?_⟩
    have hh : (capStep (z,c)).2≤z.1 := min_le_left _ _
    exact h₂.trans (max_le (by exact Nat.le_max_left _ _) (hh.trans (Nat.le_max_left _ _)))
@[fun_prop] theorem boundedValue_poly : Poly (fun z : ℕ×List Bool => boundedValue z.1 z.2) := by
  have hs : Poly capStep := by unfold capStep; fun_prop
  have hf := Poly.listFold false capStep hs (4*X+2) (by
    intro z k
    obtain ⟨h₁,h₂⟩ := capStep_fold_bound (z.1.take k) z.2
    simp only [code_pair_length,code_nat_length,h₁,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
  unfold boundedValue
  exact Poly.second _ (Poly.comp _ (fun z : ℕ×List Bool => (z.2.reverse,(z.1,0))) hf (by fun_prop))

lemma log2_bits_length (n : ℕ) : n.log2=n.bits.length-1 := by
  by_cases hn : n=0
  · simp [hn]
  have h₁ := (Nat.lt_size).mpr (Nat.log2_self_le hn)
  have h₂ := (Nat.size_le).mpr (Nat.lt_log2_self (n := n))
  rw [←Nat.size_eq_bits_len] at h₁ h₂
  omega
lemma bits_nil_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  rw [←List.length_eq_zero_iff,Nat.size_eq_bits_len,Nat.size_eq_zero]
end BinaryMatching.Parse
end

end OAI
