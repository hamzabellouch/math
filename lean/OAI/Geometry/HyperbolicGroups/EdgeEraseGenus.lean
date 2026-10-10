import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PermErasePair
import OAI.Geometry.HyperbolicGroups.EdgeErase
import OAI.Geometry.HyperbolicGroups.EdgeEraseComponents
import OAI.Geometry.HyperbolicGroups.PictureMapFurther

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D) (a : D)

lemma eraseEdge_euler (hne : ¬ M.face.SameCycle a (M.edge a))
    (hfixed : ¬ (M.face a = a ∧ M.face (M.edge a) = M.edge a)) :
    (M.eraseEdge a).euler = M.euler := by
  have hfa : M.face a ≠ M.edge a := by
    intro he; apply hne; rw [← he]; exact SameCycle.rfl.apply_right
  have hfb : M.face (M.edge a) ≠ a := by
    intro he
    have hh := (SameCycle.rfl (f := M.face) (x := M.edge a)).apply_right
    rw [he] at hh
    exact hne hh.symm
  have hv : M.vertex a ≠ a := hfb
  have hf : (M.face * swap a (M.edge a)) a ≠ a := by
    simpa only [mul_apply,swap_apply_left] using hfb
  have hbvp : bypass M.vertex a (M.edge a) ≠ M.edge a := by
    rw [bypass_away _ _ _ (M.edge_ne a)]
    simp only [vertex,mul_apply,M.edge_edge]
    by_cases h : M.face a = a
    · rw [ite_eq_left h]; exact fun hb => hfixed ⟨h,hb⟩
    · rw [ite_eq_right h]; exact hfa
  have hbfp : bypass (M.face * swap a (M.edge a)) a (M.edge a) ≠ M.edge a := by
    simpa only [bypass_away _ _ _ (M.edge_ne a),vertex,mul_apply,M.edge_edge,
      swap_apply_right,swap_apply_left] using hbvp
  have hcV := erasePair_cycles M.vertex (M.edge_ne a).symm hv hbvp
  have hcF := erasePair_cycles (M.face * swap a (M.edge a)) (M.edge_ne a).symm hf hbfp
  have hm := cycles_merge_right M.face hne
  have hD := card_offPair (M.edge_ne a).symm
  rw [euler,euler,M.eraseEdge_vertex_perm a,hcV]
  change cycles M.vertex + cycles (erasePair (M.face * swap a (M.edge a)) (M.edge_ne a).symm) - _ = _
  rw [hcF]
  omega

/-- Deleting an edge separating two distinct face cycles preserves actual
combinatorial genus zero, including the component consisting of two monogons. -/
theorem eraseEdge_genusZero (hG : M.GenusZero)
    (hne : ¬ M.face.SameCycle a (M.edge a)) : (M.eraseEdge a).GenusZero := by
  by_cases hfixed : M.face a = a ∧ M.face (M.edge a) = M.edge a
  · have hinv := offPair_invariant hfixed.1 hfixed.2
    have heq : M.eraseEdge a = M.restrict (OffPair a (M.edge a)) hinv (M.eraseEdge_invariant a) := by
      apply PictureMap.ext
      · ext x
        change bypassPair (M.face * swap a (M.edge a)) a (M.edge a) x.val = M.face x.val
        have hx := (hinv x.val).mpr x.property
        rw [bypassPair,bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
        simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,
          ite_eq_right hx.1,ite_eq_right hx.2]
      · rfl
    rw [heq]
    exact M.restrict_genusZero _ hG hinv (M.eraseEdge_invariant a)
  · obtain ⟨c,ha,hb⟩ := M.eraseEdge_component_witness a hne hfixed
    have hc := M.eraseEdge_components_le a c ha hb
    have he := M.eraseEdge_euler a hne hfixed
    have hh := (M.eraseEdge a).euler_le
    change M.euler = _ at hG
    change (M.eraseEdge a).euler = _
    omega

end HyperbolicObstruction.PictureSwitch.PictureMap
end

end OAI
