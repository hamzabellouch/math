import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureGenus
import OAI.Geometry.HyperbolicGroups.PermErasePair
import OAI.Geometry.HyperbolicGroups.EdgeErase

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D) (a : D)

/-- When the spliced face retains a side, deleting its paired edge cannot
create a new component. This is a quotient-of-darts proof, not a drawing. -/
lemma eraseEdge_components_le (c : {x // OffPair a (M.edge a) x})
    (ha : (M.face * swap a (M.edge a)).SameCycle a c.val)
    (hb : (M.face * swap a (M.edge a)).SameCycle (M.edge a) c.val) :
    Nat.card (Quotient (M.eraseEdge a).components) ≤ Nat.card (Quotient M.components) := by
  let rep : D → {x // OffPair a (M.edge a) x} :=
    fun x => if hx : OffPair a (M.edge a) x then ⟨x,hx⟩ else c
  let j : D → Quotient (M.eraseEdge a).components :=
    fun x => Quotient.mk _ (rep x)
  have hr (x : D) : (M.face * swap a (M.edge a)).SameCycle x (rep x).val := by
    by_cases hx : OffPair a (M.edge a) x
    · simp only [rep,dite_eq_left hx]; exact SameCycle.rfl
    · simp only [rep,dite_eq_right hx]
      have hx' : x = a ∨ x = M.edge a := by unfold OffPair at hx; tauto
      rcases hx' with rfl | rfl
      · exact ha
      · exact hb
  have hf : ∀ x y, (M.face * swap a (M.edge a)).SameCycle x y → j x = j y := by
    intro x y hxy
    apply Quotient.sound
    apply (M.eraseEdge a).face_le_components
    apply (M.eraseEdge_face_orbits a _ _).mpr
    exact (hr x).symm.trans (hxy.trans (hr y))
  have hrepA : rep a = c := dite_eq_right (fun h => h.1 rfl)
  have hrepB : rep (M.edge a) = c := dite_eq_right (fun h => h.2 rfl)
  have hswap : ∀ x, j (swap a (M.edge a) x) = j x := by
    intro x
    by_cases hxa : x = a
    · subst x
      rw [swap_apply_left]
      exact congrArg (Quotient.mk (M.eraseEdge a).components) (hrepB.trans hrepA.symm)
    by_cases hxb : x = M.edge a
    · subst x
      rw [swap_apply_right]
      exact congrArg (Quotient.mk (M.eraseEdge a).components) (hrepA.trans hrepB.symm)
    · rw [swap_apply_of_ne_of_ne hxa hxb]
  have he : ∀ x, j x = j (M.edge x) := by
    intro x
    by_cases hx : OffPair a (M.edge a) x
    · have hx' := (M.eraseEdge_invariant a x).mpr hx
      simp only [j,rep,dite_eq_left hx,dite_eq_left hx']
      apply Quotient.sound
      exact (M.eraseEdge a).edge_le_components (SameCycle.rfl (f := (M.eraseEdge a).edge) (x := ⟨x,hx⟩)).apply_right
    · have hx' : ¬ OffPair a (M.edge a) (M.edge x) :=
        fun h => hx ((M.eraseEdge_invariant a x).mp h)
      simp only [j,rep,dite_eq_right hx,dite_eq_right hx']
  have hj : M.components ≤ Setoid.ker j := by
    apply M.components_le
    · intro x
      have hh := hf (swap a (M.edge a) x) (M.face x) (by
        have hz := (SameCycle.rfl (f := M.face * swap a (M.edge a))
          (x := swap a (M.edge a) x)).apply_right
        simpa only [mul_apply,swap_apply_self] using hz)
      exact (hswap x).symm.trans hh
    · exact he
  let q : Quotient M.components → Quotient (M.eraseEdge a).components :=
    Quotient.lift j (fun _ _ h => hj h)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,rfl⟩ := Quotient.exists_rep y
    refine ⟨Quotient.mk _ x.val,?_⟩
    change j x.val = Quotient.mk _ x
    simp only [j,rep,dite_eq_left x.property]
  let : Fintype (Quotient M.components) := Fintype.ofFinite _
  let : Fintype (Quotient (M.eraseEdge a).components) := Fintype.ofFinite _
  simpa only [← Nat.card_eq_fintype_card] using Fintype.card_le_of_surjective q hq

lemma eraseEdge_component_witness (hne : ¬ M.face.SameCycle a (M.edge a))
    (hfixed : ¬ (M.face a = a ∧ M.face (M.edge a) = M.edge a)) :
    ∃ c : {x // OffPair a (M.edge a) x},
      (M.face * swap a (M.edge a)).SameCycle a c.val ∧
      (M.face * swap a (M.edge a)).SameCycle (M.edge a) c.val := by
  have hab : (M.face * swap a (M.edge a)).SameCycle a (M.edge a) :=
    sameCycle_after_swap_right M.face hne
  have hfa : M.face a ≠ M.edge a := by
    intro he; apply hne; rw [← he]; exact SameCycle.rfl.apply_right
  have hfb : M.face (M.edge a) ≠ a := by
    intro he
    have hh := (SameCycle.rfl (f := M.face) (x := M.edge a)).apply_right
    rw [he] at hh
    exact hne hh.symm
  by_cases haa : M.face a = a
  · have hbb : M.face (M.edge a) ≠ M.edge a := fun h => hfixed ⟨haa,h⟩
    have hc : (M.face * swap a (M.edge a)).SameCycle a (M.face (M.edge a)) := by
      simpa only [mul_apply,swap_apply_left] using
        (SameCycle.rfl (f := M.face * swap a (M.edge a)) (x := a)).apply_right
    exact ⟨⟨M.face (M.edge a),hfb,hbb⟩,hc,hab.symm.trans hc⟩
  · have hc : (M.face * swap a (M.edge a)).SameCycle (M.edge a) (M.face a) := by
      simpa only [mul_apply,swap_apply_right] using
        (SameCycle.rfl (f := M.face * swap a (M.edge a)) (x := M.edge a)).apply_right
    exact ⟨⟨M.face a,haa,hfa⟩,hab.trans hc,hc⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end

end OAI
