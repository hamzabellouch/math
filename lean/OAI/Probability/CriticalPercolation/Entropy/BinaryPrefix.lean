import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryWords
import OAI.Probability.CriticalPercolation.Entropy.BinarySwitches

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

lemma anchors_prefix_getElem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < k+2) :
    (anchors d x k (historyPrefix n h k))[i]? = (anchors d x n h)[i]? := by
  induction n with
  | zero => have he : k=0 := by omega
            subst k
            rw [prefix_self]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; rw [prefix_self]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev n h k hk',ih h.1 hk']
      change _ = (anchors d x n h.1 ++ [_])[i]?
      rw [List.getElem?_append_left (by rw [anchors_length]; omega)]

lemma node_prefix (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < k+2) :
    node d x k (historyPrefix n h k) i = node d x n h i := by
  simp only [node,anchors_prefix_getElem d x n h k hk i hi]

lemma nodeMark_prefix (n : ℕ) (h : History E n) (k : ℕ) (hk : k ≤ n)
    (i : ℕ) (hi : i < k+2) : nodeMark k (historyPrefix n h k) i = nodeMark n h i := by
  induction n with
  | zero => have he : k=0 := by omega
            subst k
            rw [prefix_self]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; rw [prefix_self]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev n h k hk',ih h.1 hk',nodeMark_old n h i (by omega)]

lemma marks_nodeMark (n : ℕ) (h : History E n) (i : Fin n) :
    marks n h i = nodeMark n h (i.val+2) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [marks,Fin.snoc_last,Fin.val_last,nodeMark_current]
    · rw [marks,Fin.snoc_castSucc,ih h.1 j,nodeMark_old n h _ (by simp)]
      rfl

lemma targets_prefix (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) :
    targets d x n h (k+2) = anchorSet d x k (historyPrefix n h k) := by
  ext v
  constructor
  · rintro ⟨j,hj,hjv⟩
    refine ⟨(node d x k (historyPrefix n h k) j).2,?_⟩
    have hm := node_mem d x k (historyPrefix n h k) j hj
    rw [node_prefix d x n h k hk j hj] at hm ⊢
    have heq : node d x n h j = (v, (node d x n h j).2) := Prod.ext hjv rfl
    rw [← heq]
    exact hm
  · rintro ⟨b,hb⟩
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    have hjlt : j < k+2 := by
      have ht := List.getElem?_eq_some_iff.mp hj
      simpa only [anchors_length] using ht.1
    have hnode : node d x k (historyPrefix n h k) j = (v,b) := by
      simp only [node,hj,Option.getD_some]
    exact ⟨j,hjlt,congrArg Prod.fst ((node_prefix d x n h k hk j hjlt).symm.trans hnode)⟩

lemma current_prefix_anchor (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k < n) :
    (node d x n h (k+2)).1 = x (nextIndex d k (historyPrefix n h k)) := by
  have he := node_prefix d x n h (k+1) hk (k+2) (by omega)
  rw [←he,node_current]
  have hp : (historyPrefix n h (k+1)).1 = historyPrefix n h k := by
    clear he
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn : k=n
      · subst k; rw [prefix_self,prefix_last]
      · have hk' : k<n := by omega
        rw [prefix_prev n h (k+1) (by omega),prefix_prev n h k hk'.le]
        exact ih h.1 hk'
  rw [hp]

end CriticalPercolation.BinaryLaw
end
end

end OAI
