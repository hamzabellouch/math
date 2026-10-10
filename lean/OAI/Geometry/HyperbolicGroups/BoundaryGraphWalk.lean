import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm SimpleGraph
attribute [local instance] Classical.propDecidable
variable {D V : Type*} [DecidableEq D] {p : Perm D} {G : SimpleGraph V}
variable {xs : List D} (h : IsBoundary p xs) (j : D → G.Dart)
  (hc : ∀ x ∈ xs, (j (p x)).fst = (j x).snd)

include h hc in
lemma IsBoundary.graph_chain : (xs.map j).IsChain G.DartAdj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hl : i+1 < xs.length := by simpa only [List.length_map] using hi
  have hi' : i < xs.length := by omega
  simp only [List.getElem_map]
  change (j xs[i]).snd = (j xs[i+1]).fst
  have he := hc xs[i] (List.getElem_mem hi')
  rw [h.turn _ (List.getElem_mem hi'),List.formPerm_apply_getElem _ h.nodup] at he
  simpa only [Nat.mod_eq_of_lt hl] using he.symm

include h hc in
/-- Read a literal permutation face as an actual graph closed walk. -/
lemma IsBoundary.graph_closed_walk (hne : xs ≠ []) :
    ∃ (v : V) (q : G.Walk v v), q.darts = xs.map j := by
  have hn : xs.map j ≠ [] := by
    intro hh
    exact hne (List.map_eq_nil_iff.mp hh)
  let q := Walk.ofDarts (xs.map j) hn (h.graph_chain j hc)
  have he : ((xs.map j).getLast hn).snd = ((xs.map j).head hn).fst := by
    rw [List.getLast_map,List.head_map]
    have hh := hc (xs.getLast hne) (List.getLast_mem hne)
    rw [h.turn _ (List.getLast_mem hne)] at hh
    have hp : xs.formPerm (xs.getLast hne) = xs.head hne := by
      cases xs with
      | nil => contradiction
      | cons a xs => exact List.formPerm_apply_getLast a xs
    rw [hp] at hh
    exact hh.symm
  refine ⟨((xs.map j).head hn).fst,q.copy rfl he,?_⟩
  rw [Walk.darts_copy]
  exact Walk.darts_ofDarts hn (h.graph_chain j hc)

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
