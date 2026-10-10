import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseRealExpectation

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

abbrev History (α : Type) := α × List α

def extend (h : History α) (a : α) : History α := (a,h.1::h.2)

def branch (κ : α → SparseIntegerLaw α) (h : History α) : SparseIntegerLaw (History α) :=
  (κ h.1).map (extend h)

def tree (κ : ℕ → α → SparseIntegerLaw α) (a : α) : ℕ → SparseIntegerLaw (History α)
  | 0 => .dirac (a,[])
  | t+1 => (tree κ a t).bindIndexed (fun i => branch (κ t) (tree κ a t).states[i.val])

theorem tree_length (κ : ℕ → α → SparseIntegerLaw α) (a : α) (B : ℕ)
    (hB : ∀ t s, (κ t s).length ≤ B) (t : ℕ) : (tree κ a t).length ≤ B^t := by
  induction t with
  | zero => simp only [tree,SparseIntegerLaw.dirac,pow_zero,le_refl]
  | succ t ih =>
    exact (SparseIntegerLaw.bindIndexed_length _ _ B (fun i => hB t _)).trans
      ((Nat.mul_le_mul_right B ih).trans_eq (pow_succ B t).symm)

theorem tree_property (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (P : ℕ → History α → Prop) (h0 : P 0 (a,[]))
    (hstep : ∀ t h, P t h → ∀ i : Fin (κ t h.1).length, P (t+1) (extend h (κ t h.1).states[i.val]))
    (t : ℕ) : ∀ i : Fin (tree κ a t).length, P t (tree κ a t).states[i.val] := by
  induction t with
  | zero => intro i; simpa only [tree,SparseIntegerLaw.dirac,Vector.getElem_replicate] using h0
  | succ t ih =>
    apply SparseIntegerLaw.bindIndexed_property _ _ (P (t+1))
    intro i j
    have hh := SparseIntegerLaw.map_states (κ t (tree κ a t).states[i.val].1)
      (extend (tree κ a t).states[i.val]) j
    change (branch (κ t) (tree κ a t).states[i.val]).states[j.val]=_ at hh
    rw [hh]
    exact hstep t _ (ih i) j

theorem past_length (κ : ℕ → α → SparseIntegerLaw α) (a : α) (t : ℕ)
    (i : Fin (tree κ a t).length) : ((tree κ a t).states[i.val].2).length=t := by
  exact tree_property κ a (fun t h => h.2.length=t) rfl
    (fun t h hh j => by simp only [extend,List.length_cons,hh]) t i

theorem physical_invariant (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (P : α → Prop) (h0 : P a)
    (hstep : ∀ t s, P s → ∀ i : Fin (κ t s).length, P (κ t s).states[i.val])
    (t : ℕ) (i : Fin (tree κ a t).length) : P (tree κ a t).states[i.val].1 :=
  tree_property κ a (fun _ h => P h.1) h0 (fun t h hh j => hstep t h.1 hh j) t i

theorem expectation_step (κ : ℕ → α → SparseIntegerLaw α) (a : α) (t : ℕ)
    (V : History α → ℝ) :
    (tree κ a (t+1)).expectation V=
      (tree κ a t).expectation (fun h => (κ t h.1).expectation (fun s => V (extend h s))) := by
  rw [tree,SparseIntegerLaw.expectation_bindIndexed]
  simp_rw [branch,SparseIntegerLaw.expectation_map]
  rfl

end MetricKMedian.SparseHistories
end
end

end OAI
