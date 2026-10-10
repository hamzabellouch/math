import Mathlib
import OAI.Combinatorics.UniformKServer.TreeParking

namespace OAI

                                   
section

/-! Literal ancestry in a finite ordered rooted tree, including all internal
parks and the root. -/
noncomputable section
namespace UniformKServer.TreeAncestry
open Finset TreeRounding TreeParking
open scoped Classical
variable {n k : ℕ} {S : Shape n}

def edge (S : Shape n) (u v : Vertex n) : Prop := v ≠ 0 ∧ S.parent v=u
def descends (S : Shape n) : Vertex n → Vertex n → Prop := Relation.ReflTransGen (edge S)
def subtree (S : Shape n) (u : Vertex n) : Finset (Vertex n) := univ.filter (descends S u)

def depth (S : Shape n) (v : Vertex n) : ℕ := if hv : v=0 then 0 else depth S (S.parent v)+1
termination_by v.val
decreasing_by exact S.earlier v hv

theorem depth_root : depth S 0=0 := by rw [depth,dite_eq_left rfl]
theorem depth_child (v : Vertex n) (hv : v ≠ 0) : depth S v=depth S (S.parent v)+1 := by rw [depth,dite_eq_right hv]

theorem desc_refl (v : Vertex n) : descends S v v := .refl

theorem desc_tail {u v w : Vertex n} (h : descends S u v) (hw : w ≠ 0) (hp : S.parent w=v) :
    descends S u w := h.tail ⟨hw,hp⟩

theorem desc_val {u v : Vertex n} (h : descends S u v) : u.val ≤ v.val := by
  induction h with
  | refl => rfl
  | @tail v w h e ih =>
    have hh := S.earlier w e.1
    rw [e.2] at hh
    omega

theorem desc_depth {u v : Vertex n} (h : descends S u v) : depth S u ≤ depth S v := by
  induction h with
  | refl => rfl
  | @tail v w h e ih => rw [depth_child w e.1,e.2]; omega

theorem desc_same_depth {u v : Vertex n} (h : descends S u v) (he : depth S u=depth S v) : u=v := by
  rcases h.cases_tail with hv | ⟨w,hw,e⟩
  · exact hv.symm
  · have hd := desc_depth hw
    rw [depth_child v e.1,e.2] at he
    omega

theorem subtree_closed (u v : Vertex n) (hv : v ≠ 0) (hp : S.parent v ∈ subtree S u) :
    v ∈ subtree S u := by
  simp only [subtree,mem_filter,mem_univ,true_and] at *
  exact desc_tail hp hv rfl

theorem subtree_boundary (u : Vertex n) : boundary (S:=S) (subtree S u)={u} := by
  ext v
  simp only [boundary,mem_filter,subtree,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨h,hv | hp⟩
    · subst v
      have hh := desc_val h
      apply Fin.ext
      exact (Nat.le_zero.mp hh).symm
    · rcases h.cases_tail with hv | ⟨w,hw,e⟩
      · exact hv
      · exact (hp (e.2.symm ▸ hw)).elim
  · intro hv
    subst v
    refine ⟨desc_refl u,?_⟩
    by_cases hu : u=0
    · exact Or.inl hu
    · right
      intro h
      have hh := desc_val h
      have he := S.earlier u hu
      omega

theorem subtree_total (a : Allocation S k) (u : Vertex n) :
    (∑ v ∈ subtree S u, park S a.amount v)=a.amount u := by
  rw [cut a (subtree S u) (subtree_closed u),subtree_boundary,sum_singleton]

def ancestor (S : Shape n) (j : ℕ) (v : Vertex n) : Vertex n :=
  if _h : depth S v ≤ j then v else ancestor S j (S.parent v)
termination_by v.val
decreasing_by
  apply S.earlier
  intro he
  subst v
  exact _h (by rw [depth_root]; omega)

theorem ancestor_spec (j : ℕ) (v : Vertex n) (hj : j ≤ depth S v) :
    depth S (ancestor S j v)=j ∧ descends S (ancestor S j v) v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    rw [ancestor]
    split_ifs with hv
    · exact ⟨le_antisymm hv hj,desc_refl v⟩
    · have h0 : v ≠ 0 := by intro hh; subst v; exact hv (by rw [depth_root]; omega)
      have hp : j ≤ depth S (S.parent v) := by rw [depth_child v h0] at hj hv; omega
      have hh := ih (S.parent v) (S.earlier v h0) hp
      exact ⟨hh.1,desc_tail hh.2 h0 rfl⟩

theorem same_ancestor {u v w : Vertex n} (hu : descends S u w) (hv : descends S v w)
    (hd : depth S u=depth S v) : u=v := by
  induction w using WellFounded.induction (measure Fin.val).wf with
  | h w ih =>
    by_cases huw : u=w
    · subst u
      exact (desc_same_depth hv hd.symm).symm
    by_cases hvw : v=w
    · subst v
      exact desc_same_depth hu hd
    rcases hu.cases_tail with hw | ⟨p,hp,he⟩
    · exact (huw hw.symm).elim
    rcases hv.cases_tail with hw | ⟨q,hq,hf⟩
    · exact (hvw hw.symm).elim
    have hup : descends S u (S.parent w) := he.2.symm ▸ hp
    have hvp : descends S v (S.parent w) := hf.2.symm ▸ hq
    exact ih (S.parent w) (S.earlier w he.1) hup hvp

theorem ancestor_unique (j : ℕ) {u v : Vertex n} (h : descends S u v) (hd : depth S u=j) :
    ancestor S j v=u := by
  have ha := ancestor_spec j v (by rw [←hd]; exact desc_depth h)
  exact same_ancestor ha.2 h (ha.1.trans hd.symm)

end UniformKServer.TreeAncestry

end


end

end OAI
