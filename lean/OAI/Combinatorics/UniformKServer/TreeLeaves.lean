import Mathlib
import OAI.Combinatorics.UniformKServer.TreeAncestry

namespace OAI

                                 
section

/-! Unique child on a leaf path and conservation of literal hidden counts. -/
noncomputable section
namespace UniformKServer.TreeLeaves
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {n : ℕ} {S : Shape n}

def leaf (v : Vertex n) : Prop := ∀ _u : Children S v, False

theorem root_descends (v : Vertex n) : descends S 0 v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v; exact desc_refl 0
    · exact desc_tail (ih (S.parent v) (S.earlier v hv)) hv rfl

theorem child_path (v w : Vertex n) (hw : leaf (S:=S) w) (hv : Nonempty (Children S v))
    (h : descends S v w) : ∃! c : Children S v, descends S c.val w := by
  rcases h.cases_head with he | ⟨u,hu,huw⟩
  · subst w
    exact (hw (Classical.choice hv)).elim
  · let c : Children S v := ⟨u,hu⟩
    refine ⟨c,huw,?_⟩
    intro d hd
    apply Subtype.ext
    exact same_ancestor hd huw (by rw [depth_child _ d.property.1,depth_child _ hu.1,d.property.2,hu.2])

def indicator (v w : Vertex n) : ℕ := if descends S v w then 1 else 0

theorem indicator_root (w : Vertex n) : indicator (S:=S) 0 w=1 := ite_eq_left (root_descends w)

theorem indicator_children (v w : Vertex n) (hw : leaf (S:=S) w) (hv : Nonempty (Children S v)) :
    (∑ c : Children S v, indicator (S:=S) c.val w)=indicator (S:=S) v w := by
  by_cases h : descends S v w
  · obtain ⟨c,hc,hu⟩ := child_path v w hw hv h
    rw [sum_eq_single c]
    · simp only [indicator,ite_eq_left h,ite_eq_left hc]
    · intro d _ hdc
      exact ite_eq_right (fun hd => hdc (hu d hd))
    · simp
  · have hz (c : Children S v) : indicator (S:=S) c.val w=0 := by
      apply ite_eq_right
      intro hc
      exact h (hc.head c.property)
    rw [show indicator (S:=S) v w=0 from ite_eq_right h]
    exact sum_eq_zero (fun c _ => hz c)

def count {k : ℕ} (p : Fin k → Vertex n) (v : Vertex n) : ℕ := ∑ a, indicator (S:=S) v (p a)

theorem count_le {k : ℕ} (p : Fin k → Vertex n) (v : Vertex n) : count (S:=S) p v ≤ k := by
  calc
    _ ≤ ∑ _ : Fin k, 1 := sum_le_sum fun a _ => by unfold indicator; split_ifs <;> omega
    _ = _ := by simp

theorem count_root {k : ℕ} (p : Fin k → Vertex n) : count (S:=S) p 0=k := by
  simp [count,indicator_root]

theorem count_children {k : ℕ} (p : Fin k → Vertex n) (hp : ∀ a, leaf (S:=S) (p a))
    (v : Vertex n) (hv : Nonempty (Children S v)) :
    (∑ c : Children S v, count (S:=S) p c.val)=count (S:=S) p v := by
  unfold count
  rw [sum_comm]
  simp only [indicator_children v _ (hp _) hv]

end UniformKServer.TreeLeaves

end


end

end OAI
