import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeMappedWalk
import OAI.Geometry.HyperbolicGroups.RelativeApexLocal

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

/-- The actual simple macro polygon carried by one free source face. Its
vertices are the original TEMPLATE vertices in their original cyclic order,
not the possibly identified letter-bouquet vertices. This supplies the finite
macro-cycle perimeter/three-fan bounds from the produced normal picture. -/
noncomputable def mappedMacroPolygon (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (.inl (a,e))) :
    MacroGraph.Polygon := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  let b : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfree (y : I) : (target n w d ell hell word c hc f).free
      ((target n w d ell hell word c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  have hclose (y : I) : (j (q y)).fst = (j y).snd := by
    have h := P.closed y.val
    change (target n w d ell hell word c hc f).front (P.index (q y).val) = (target n w d ell hell word c hc f).back (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj h))
  exact {
    n := Fintype.card I
    vertex := fun i => (j (b i)).fst
    next := b.trans (q.trans b.symm)
    injective := by
      intro i k hik
      apply b.injective
      apply Subtype.ext
      apply P.simple_front hs (hfree (b i)) ((b i).property.symm.trans (b k).property)
      rw [hj,hj]
      exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl hik))
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

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
