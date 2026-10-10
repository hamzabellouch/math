import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeWalkTarget
import OAI.Geometry.HyperbolicGroups.WalkRadial

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma walkKind_cycle {x y : P.Dart} (h : P.pairing.face.SameCycle x y) :
    walkKind n w d (P.index x) = walkKind n w d (P.index y) := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle
    (t := (1 : Perm (WalkKind n w d))) P.kind h)

lemma same_top_face {x y : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (a,e)) (h : P.pairing.face.SameCycle x y) :
    ∃ e', P.index y = .inl (a,e') := by
  have hk := walkKind_cycle n w d c hc f P h
  rw [hx] at hk
  cases hy : P.index y with
  | inl s =>
    rw [hy] at hk
    have hs : a = s.1 := Sum.inl.inj hk
    exact ⟨s.2,by rw [hs]⟩
  | inr s => rw [hy] at hk; cases hk

/-- The actual simple macro polygon carried by one free source face. Its
vertices are the original TEMPLATE vertices in their original cyclic order,
not the possibly identified letter-bouquet vertices. This supplies the finite
macro-cycle perimeter/three-fan bounds from the produced normal picture. -/
noncomputable def mappedMacroPolygon (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (a,e)) :
    MacroGraph.Polygon := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (same_top_face n w d c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (a,j y) :=
    (same_top_face n w d c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  let b : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfree (y : I) : (walkTarget n w d c hc f).free
      ((walkTarget n w d c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  have hclose (y : I) : (j (q y)).fst = (j y).snd := by
    have h := P.closed y.val
    change walkFront n w d (P.index (q y).val) = walkBack n w d (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj h)
  exact {
    n := Fintype.card I
    vertex := fun i => (j (b i)).fst
    next := b.trans (q.trans b.symm)
    injective := by
      intro i k hik
      apply b.injective
      apply Subtype.ext
      apply P.simple_front hs (hfree (b i)) ((b i).property.symm.trans (b k).property)
      change walkFront n w d (P.index (b i).val) = walkFront n w d (P.index (b k).val)
      rw [hj,hj]
      exact congrArg Sum.inl (Prod.ext rfl hik)
    adjacent := by
      intro i
      change MacroGraph.Adjacent (j (b i)).fst (j (b (b.symm (q (b i))))).fst
      rw [b.apply_symm_apply,hclose]
      exact (j (b i)).adj
    no_backtrack := by
      intro i hi
      have hv := congrArg (fun k => (b k).val) hi
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hv
      exact hb (b i).val (hfree (b i)) hv }

lemma mappedMacroPolygon_size (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (a,e)) :
    (mappedMacroPolygon n w d c hc f P hs hb x a e hx).n =
      Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} := rfl

/-- Source normal-form output now has all the actual macro cardinal bounds;
no `Polygon` or perimeter field is assumed of the raw picture. -/
theorem normalizedMacroRows : ∃ Q : WalkPicture.{u} (walkTarget n w d c hc f),
    Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧ Q.Reduced ∧
      Q.RadialInjective (isApex n w) ∧ Q.chain = P.chain ∧
      ∀ (hs : Q.Simple) (hb : Q.NoBigon) (x : Q.Dart) (a : Top n w)
        (e : MacroGraph.graph.Dart) (hx : Q.index x = .inl (a,e)),
        Fintype.card {y : Q.Dart // Q.pairing.face.SameCycle x y} ≤ 15 ∧
          3 ≤ (mappedMacroPolygon n w d c hc f Q hs hb x a e hx).points.card := by
  obtain ⟨Q,hr,hs,hb,hred,hrad,hchain⟩ := P.normalize_radial (isApex n w)
    (fun s => radial n w (walkLabel n w d s))
  refine ⟨Q,hr,hs,hb,hred,hrad,hchain,?_⟩
  intro hs hb x a e hx
  let B := mappedMacroPolygon n w d c hc f Q hs hb x a e hx
  constructor
  · exact B.perimeter_le
  · apply B.points_ge
    change 0 < Fintype.card {y : Q.Dart // Q.pairing.face.SameCycle x y}
    exact Fintype.card_pos_iff.mpr ⟨⟨x,SameCycle.rfl⟩⟩

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
