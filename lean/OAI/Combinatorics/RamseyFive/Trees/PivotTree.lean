import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SequentialLaw
import OAI.Combinatorics.RamseyFive.Entropy.FinitePiLaw

namespace OAI

namespace SharpRamseyFive.PivotTree
open BinaryTree

def balanced (lo : ℕ) : ℕ → BinaryTree ℕ
  | 0 => .nil
  | n+1 => .node (lo+n/2) (balanced lo (n/2))
      (balanced (lo+n/2+1) (n-n/2))
termination_by n => n

def inorder {α : Type*} : BinaryTree α → List α
  | .nil => []
  | .node a l r => inorder l ++ a :: inorder r

lemma balanced_nodes (lo n : ℕ) : (balanced lo n).numNodes=n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    cases n with
    | zero => simp [balanced]
    | succ n =>
      rw [balanced,BinaryTree.numNodes,ih (n/2) (by omega),ih (n-n/2) (by omega)]
      omega

lemma balanced_height (H lo n : ℕ) (hn : n<2^H) :
    (balanced lo n).height≤H := by
  induction H generalizing lo n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simp [balanced]
  | succ H ih =>
    cases n with
    | zero => simp [balanced]
    | succ n =>
      rw [pow_succ] at hn
      have hl : n/2<2^H := by omega
      have hr : n-n/2<2^H := by omega
      simp only [balanced,BinaryTree.height]
      exact Nat.succ_le_succ (max_le (ih lo (n/2) hl) (ih _ _ hr))

lemma balanced_inorder (lo n : ℕ) : inorder (balanced lo n)=List.range' lo n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    cases n with
    | zero => simp [balanced,inorder]
    | succ n =>
      rw [balanced,inorder,ih (n/2) (by omega),ih (n-n/2) (by omega)]
      rw [←List.range'_succ]
      have he : lo+n/2=lo+1*(n/2) := by omega
      rw [he,List.range'_append]
      have he' : n/2+(n-n/2+1)=n+1 := by omega
      rw [he']

def rootValue {α : Type*} (f : α→ℝ) : BinaryTree α→ℝ
  | .nil => 0
  | .node a _ _ => f a

def total {α : Type*} (f : α→ℝ) : BinaryTree α→ℝ
  | .nil => 0
  | .node a l r => f a+total f l+total f r

def Controls {α : Type*} (f : α→ℝ) (B : ℝ) : BinaryTree α→Prop
  | .nil => True
  | .node a l r => 0≤f a ∧ rootValue f l+rootValue f r≤f a+B ∧
      Controls f B l ∧ Controls f B r

lemma root_nonneg {α : Type*} {f : α→ℝ} {B : ℝ} {t : BinaryTree α}
    (h : Controls f B t) : 0≤rootValue f t := by
  cases t with
  | nil => rfl
  | node a l r => exact h.1

theorem total_le_height {α : Type*} (f : α→ℝ) {B : ℝ} (hB : 0≤B)
    (t : BinaryTree α) (ht : Controls f B t) :
    total f t ≤ t.height*(rootValue f t+B*t.numNodes) := by
  induction t with
  | nil => simp [total,rootValue]
  | node a l r ihl ihr =>
    obtain ⟨ha,hc,hl,hr⟩ := ht
    have hln := root_nonneg hl
    have hrn := root_nonneg hr
    have hle : (l.height:ℝ)≤ max l.height r.height := by exact_mod_cast le_max_left l.height r.height
    have hre : (r.height:ℝ)≤ max l.height r.height := by exact_mod_cast le_max_right l.height r.height
    have h₁ := (ihl hl).trans (mul_le_mul_of_nonneg_right hle (add_nonneg hln (mul_nonneg hB (Nat.cast_nonneg _))))
    have h₂ := (ihr hr).trans (mul_le_mul_of_nonneg_right hre (add_nonneg hrn (mul_nonneg hB (Nat.cast_nonneg _))))
    have h₃ := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (max l.height r.height))
    simp only [total,BinaryTree.height,BinaryTree.numNodes,rootValue,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hB (Nat.cast_nonneg l.numNodes),mul_nonneg hB (Nat.cast_nonneg r.numNodes)]

def prune {α : Type*} (keep : α→Bool) : BinaryTree α→BinaryTree α
  | .nil => .nil
  | .node a l r => if keep a then .node a (prune keep l) (prune keep r) else .nil

lemma prune_height {α : Type*} (keep : α→Bool) (t : BinaryTree α) :
    (prune keep t).height≤t.height := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    simp only [prune]
    split
    · exact Nat.succ_le_succ (max_le_max hl hr)
    · exact Nat.zero_le _

lemma prune_nodes {α : Type*} (keep : α→Bool) (t : BinaryTree α) :
    (prune keep t).numNodes≤t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    simp only [prune]
    split
    · simp only [BinaryTree.numNodes];omega
    · exact Nat.zero_le _

end SharpRamseyFive.PivotTree

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)

def Tape : BinaryTree A→Type (max v w)
  | .nil => PUnit
  | .node a l r => (∀c,Ω a c) × Tape l × Tape r

noncomputable instance tapeFintype [∀a c,Fintype (Ω a c)] (t : BinaryTree A) : Fintype (Tape Ω t) := by
  induction t with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | node a l r hl hr =>
    letI := hl
    letI := hr
    exact inferInstanceAs (Fintype ((∀c,Ω a c)×Tape Ω l×Tape Ω r))

variable (left right : ∀a c t,M a c t→C)

def Message : (b : BinaryTree A)→Tape Ω b→C→Type (max z v w)
  | .nil,_,_ => PUnit
  | .node a l r,ω,c => Option ((m : M a c (ω.1 c)) ×
      Message l ω.2.1 (left a c (ω.1 c) m) × Message r ω.2.2 (right a c (ω.1 c) m))

noncomputable instance messageFintype [∀a c t,Fintype (M a c t)]
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) : Fintype (Message Ω M left right b ω c) := by
  induction b generalizing c with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | node a l r hl hr =>
    letI (m : M a c (ω.1 c)) := hl ω.2.1 (left a c (ω.1 c) m)
    letI (m : M a c (ω.1 c)) := hr ω.2.2 (right a c (ω.1 c) m)
    exact inferInstanceAs (Fintype (Option ((m : M a c (ω.1 c))×
      Message Ω M left right l ω.2.1 (left a c (ω.1 c) m)×
      Message Ω M left right r ω.2.2 (right a c (ω.1 c) m))))

noncomputable def encoded (enc : ∀a c t,Option (M a c t)) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→Message Ω M left right b ω c
  | .nil,_,_ => PUnit.unit
  | .node a l r,ω,c => (enc a c (ω.1 c)).map fun m=>⟨m,
      encoded enc l ω.2.1 (left a c (ω.1 c) m),
      encoded enc r ω.2.2 (right a c (ω.1 c) m)⟩

def retained : (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→
    Message Ω M left right b ω c→BinaryTree A
  | .nil,_,_,_ => .nil
  | .node _ _ _,_,_,none => .nil
  | .node a l r,ω,c,some ⟨m,ml,mr⟩ => .node a
      (retained l ω.2.1 (left a c (ω.1 c) m) ml)
      (retained r ω.2.2 (right a c (ω.1 c) m) mr)

omit [Fintype C] in
lemma retained_nodes_le (b : BinaryTree A) (ω : Tape Ω b) (c : C)
    (m : Message Ω M left right b ω c) :
    (retained Ω M left right b ω c m).numNodes≤b.numNodes := by
  induction b generalizing c with
  | nil => simp only [retained,BinaryTree.numNodes,le_refl]
  | node a l r hl hr =>
    cases m with
    | none => exact Nat.zero_le _
    | some m =>
      exact Nat.add_le_add (Nat.add_le_add (hl _ _ m.2.1) (hr _ _ m.2.2)) le_rfl

noncomputable def cost (localCost : ∀a c t,M a c t→ℝ) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→Message Ω M left right b ω c→ℝ
  | .nil,_,_,_ => 0
  | .node _ _ _,_,_,none => 0
  | .node a l r,ω,c,some ⟨m,ml,mr⟩ => localCost a c (ω.1 c) m+
      cost localCost l ω.2.1 (left a c (ω.1 c) m) ml+
      cost localCost r ω.2.2 (right a c (ω.1 c) m) mr

noncomputable def tapeLaw [∀a c,Fintype (Ω a c)] (p : ∀a c,Law (Ω a c)) :
    (b : BinaryTree A)→Law (Tape Ω b)
  | .nil => pureLaw PUnit.unit
  | .node a l r => adaptiveLaw (piLaw (p a)) (fun _=>
      adaptiveLaw (tapeLaw p l) (fun _=>tapeLaw p r))
end SharpRamseyFive.TreeCodec

end OAI
