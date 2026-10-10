import Mathlib

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree

open BinaryTree

def balanced (lo n : ℕ) : BinaryTree ℕ :=
  if h : n = 0 then .nil else
    .node (lo+n/2) (balanced lo (n/2))
      (balanced (lo+n/2+1) (n-n/2-1))
termination_by n
decreasing_by
  · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
  · omega

def inorder {α : Type*} : BinaryTree α → List α
  | .nil => []
  | .node a l r => inorder l ++ a :: inorder r

@[simp] lemma inorder_length {α : Type*} (t : BinaryTree α) :
    (inorder t).length=t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [inorder,hl,hr]; omega

lemma balanced_card (lo n : ℕ) : (balanced lo n).numNodes=n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with h
    · simp [h]
    · simp only [numNodes]
      rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)),
        ih (n-n/2-1) (by omega)]
      have : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      omega

lemma balanced_height (lo n : ℕ) : (balanced lo n).height≤Nat.log 2 n+1 := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with h
    · simp
    · simp only [height]
      by_cases hn : n=1
      · subst n
        simp [balanced]
      have hn2 : 2≤n := by omega
      have hl : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      have hr : n-n/2-1<n := by omega
      have hrle : n-n/2-1≤n/2 := by omega
      have h1 := ih (n/2) hl (lo:=lo)
      have h2 := ih (n-n/2-1) hr (lo:=lo+n/2+1)
      have hlog := Nat.log_monotone (b:=2) hrle
      have he := Nat.log_div_base 2 n
      have hp : 0<Nat.log 2 n := Nat.log_pos (by decide) hn2
      omega

lemma balanced_interval {lo n a : ℕ} (ha : a∈inorder (balanced lo n)) :
    lo≤a ∧ a<lo+n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced] at ha
    split_ifs at ha with h
    · simp [inorder] at ha
    · simp only [inorder,List.mem_append,List.mem_cons] at ha
      have hl : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      rcases ha with ha | ha | ha
      · have H := ih (n/2) hl ha
        omega
      · omega
      · have H := ih (n-n/2-1) (by omega) ha
        omega

def Chronological : BinaryTree ℕ → Prop
  | .nil => True
  | .node a l r => Chronological l ∧ Chronological r ∧
    (∀ b∈inorder l,b<a) ∧ (∀ b∈inorder r,a<b)

lemma balanced_chronological (lo n : ℕ) : Chronological (balanced lo n) := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with h
    · trivial
    · change Chronological (balanced lo (n/2)) ∧
        Chronological (balanced (lo+n/2+1) (n-n/2-1)) ∧ _
      refine ⟨ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)) lo,
        ih (n-n/2-1) (by omega) (lo+n/2+1),?_,?_⟩
      · intro b hb
        exact (balanced_interval hb).2
      · intro b hb
        have H := (balanced_interval hb).1
        omega

lemma inorder_pairwise {t : BinaryTree ℕ} (ht : Chronological t) :
    (inorder t).Pairwise (·<·) := by
  induction t with
  | nil => simp [inorder]
  | node a l r hl hr =>
    rcases ht with ⟨hcl,hcr,hla,har⟩
    simp only [inorder,List.pairwise_append,List.pairwise_cons]
    refine ⟨hl hcl,⟨har,hr hcr⟩,?_⟩
    intro b hb c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hla b hb
    · exact (hla b hb).trans (har c hc)

lemma balanced_nodup (lo n : ℕ) : (inorder (balanced lo n)).Nodup :=
  (inorder_pairwise (balanced_chronological lo n)).imp (fun h => ne_of_lt h)

end SharpLogRamsey.ChronologicalTree

end

end OAI
