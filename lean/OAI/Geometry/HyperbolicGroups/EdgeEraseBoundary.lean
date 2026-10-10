import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList
import OAI.Geometry.HyperbolicGroups.BoundaryRotation
import OAI.Geometry.HyperbolicGroups.BoundarySplice
import OAI.Geometry.HyperbolicGroups.BoundaryEraseList
import OAI.Geometry.HyperbolicGroups.EdgeErase

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]
namespace IsBoundary

lemma erase_head {f : Perm D} {a : D} {xs : List D} (h : IsBoundary f (a::xs)) :
    IsBoundary (bypass f a) xs := by
  refine ⟨h.nodup.of_cons,?_⟩
  intro x hx
  have ha : x ≠ a := fun he => (List.nodup_cons.mp h.nodup).1 (he ▸ hx)
  rw [← bypass_formPerm_head a xs h.nodup]
  rw [bypass_away _ _ _ ha,bypass_away _ _ _ ha,
    h.turn x (List.mem_cons_of_mem _ hx),h.turn a (by simp)]

lemma erase_at {f : Perm D} {a : D} {l r : List D} (h : IsBoundary f (l++a::r)) :
    IsBoundary (bypass f a) (l++r) := by
  have hh : IsBoundary f (a::(r++l)) := by
    simpa only [List.cons_append] using h.rotate_append
  exact hh.erase_head.rotate_append

/-- The two actual face cycles are spliced at the deleted paired sides. -/
lemma splice_heads {f : Perm D} {a b : D} {l r : List D}
    (hl : IsBoundary f (a::l)) (hr : IsBoundary f (b::r))
    (hd : ∀ x ∈ a::l, x ∉ b::r) :
    IsBoundary (f * swap a b) (a::(r++b::l)) := by
  have hl' : IsBoundary f (l++[a]) := by
    simpa using (hl.rotate_append (l := [a]) (r := l))
  have hr' : IsBoundary f (r++[b]) := by
    simpa using (hr.rotate_append (l := [b]) (r := r))
  obtain ⟨c,s,hs⟩ : ∃ c s, r++[b] = c::s := List.exists_cons_of_ne_nil (by simp)
  have hh := hl'.splice_append (hs ▸ hr') (by
    intro x hx hy
    apply hd x (by simpa only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false,false_or,or_comm] using hx)
    rw [← hs] at hy
    simpa only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false,false_or,or_comm] using hy)
  have hb : (c::s).getLast (by simp) = b := by simpa only [hs] using (List.getLast_append_singleton (a := b) r)
  rw [hb,← hs,List.append_assoc] at hh
  have hh' : IsBoundary (f*swap a b) (([a]++(r++[b]))++l) := hh.rotate_append
  simpa only [List.singleton_append,List.append_assoc,List.cons_append,List.nil_append] using hh'

omit [DecidableEq D] in
lemma splice_heads_offpair {a b : D} {l r : List D}
    (hn : (a::(r++b::l)).Nodup) : ∀ x ∈ r++l, OffPair a b x := by
  intro x hx
  have hh := List.nodup_cons.mp hn
  have hrl := List.nodup_append.mp hh.2
  refine ⟨?_,?_⟩
  · intro he
    apply hh.1
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (he ▸ hx)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (he ▸ hx))
  · intro he
    rcases List.mem_append.mp hx with hx | hx
    · exact hrl.2.2 x hx b (by simp) he
    · exact (List.nodup_cons.mp hrl.2.1).1 (he ▸ hx)

end IsBoundary
namespace PictureMap
variable (M : PictureMap D) {a : D} {l r : List D}

theorem eraseEdge_boundary (hl : IsBoundary M.face (a::l))
    (hr : IsBoundary M.face (M.edge a::r))
    (hne : ¬ M.face.SameCycle a (M.edge a)) :
    ∃ hp : ∀ x ∈ r++l, OffPair a (M.edge a) x,
      IsBoundary (M.eraseEdge a).face ((r++l).attachWith _ hp) := by
  have hs := hl.splice_heads hr (hl.disjoint hr (by simp) (by simp) hne)
  have hp := IsBoundary.splice_heads_offpair hs.nodup
  refine ⟨hp,?_⟩
  have hh : IsBoundary (bypassPair (M.face*swap a (M.edge a)) a (M.edge a)) (r++l) :=
    hs.erase_head.erase_at
  apply hh.lift hp (M.eraseEdge a).face
  intro x hx
  rfl

end PictureMap
end HyperbolicObstruction.PictureSwitch
end

end OAI
