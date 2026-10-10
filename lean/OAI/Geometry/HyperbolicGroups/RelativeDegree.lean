import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList
import OAI.Geometry.HyperbolicGroups.NormalFaceFilling

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace PolygonTarget.Boundary
variable {C L V : Type*} (B : Boundary C L V)

/-- The two orientations have exactly the same indexed perimeter. -/
lemma oriented_boundary (s : B.Side) :
    ∃ ys : List B.Side, IsBoundary B.next ys ∧ s ∈ ys ∧ ys.length = B.size s.1 := by
  rcases s with ⟨c,b,i⟩
  cases b with
  | true =>
    refine ⟨B.positiveSides c,B.positiveSides_boundary c,?_,?_⟩
    · exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · simp only [positiveSides,List.length_map,List.length_finRange]
  | false =>
    have hp := B.positiveSides_boundary c
    have hh : IsBoundary B.next ((B.positiveSides c).reverse.map B.opposite) := by
      apply hp.reverse.map B.opposite B.opposite.injective
      intro s
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
        (congrArg B.next (B.reverse_next (B.next⁻¹ s))).symm
    refine ⟨(B.positiveSides c).reverse.map B.opposite,hh,?_,?_⟩
    · apply List.mem_map.mpr
      refine ⟨⟨c,true,i⟩,List.mem_reverse.mpr ?_,rfl⟩
      exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · simp only [List.length_map,List.length_reverse,positiveSides,List.length_finRange]
end PolygonTarget.Boundary

namespace WalkPicture
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A] [DecidableEq S]
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T) {B : FrozenTarget T}

lemma FrozenMapped.face_card (hm : P.FrozenMapped B) (x : P.FrozenDart)
    (ys : List S) (hy : IsBoundary B.next ys) (hx : P.index x.val ∈ ys) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x.val y} = ys.length := by
  obtain ⟨zs,hzs,hzm,hmap⟩ := hm.pullback_boundary x hy hx
  have hb : IsBoundary P.pairing.face (zs.map Subtype.val) :=
    hzs.map Subtype.val Subtype.val_injective (fun _ => rfl)
  rw [← hb.length_eq_card (List.mem_map_of_mem hzm),List.length_map]
  simpa only [List.length_map] using congrArg List.length hmap
end WalkPicture
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))

lemma exterior_top_degree (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart)
    (hx : P.index x = .inl (.inl (a,e))) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 15 := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  have hfree (y : I) : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  apply macro_parametrization_card q j
  · intro y
    have h := P.closed y.val
    change (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (P.index (q y).val) = (exteriorWalkTarget n w d ell hell word closed c hc f).back
        (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj h))
  · intro i k hik
    apply Subtype.ext
    apply P.simple_front hs (hfree i) (i.property.symm.trans k.property)
    rw [hj,hj]
    exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl hik))
  · intro y he
    exact hb y.val (hfree y) (congrArg Subtype.val he)

lemma exterior_frozen_degree
    (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
    (x : P.Dart) (s : (frozenBoundary n w d).Side)
    (hx : P.index x = .inl (.inr s)) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 6 := by
  obtain ⟨ys,hys,hmem,hlen⟩ := (frozenBoundary n w d).oriented_boundary s
  have hxF : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index x)) = false := by
    rw [hx]; rfl
  let j : (frozenBoundary n w d).Side →
      WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell word closed :=
    fun z => .inl (.inr z)
  have hj : Function.Injective j := Sum.inl_injective.comp Sum.inr_injective
  have hys' : IsBoundary (exteriorWalkFrozen n w d ell hell word closed c hc f).next
      (ys.map j) := hys.map j hj (fun _ => rfl)
  have hh := hm.face_card P (⟨x,hxF⟩ : P.FrozenDart) (ys.map j) hys'
    (by change P.index x ∈ ys.map j; rw [hx]; exact List.mem_map_of_mem hmem)
  rw [List.length_map,hlen] at hh
  rw [hh]
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a) <;> norm_num [frozenBoundary,frozenCell,size]

/-- The actual interior dual multigraph of a protected normal disk has the
source's uniform bound15. The arbitrary exterior degree is not bounded. -/
theorem exterior_interior_degree (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
    (x : P.Dart)
    (hx : ¬ (walkTarget n w d c hc f).isExterior ell hell word closed (P.index x)) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 15 := by
  cases hi : P.index x with
  | inl s =>
    cases s with
    | inl s => exact exterior_top_degree n w d ell hell word closed c hc f P hs hb x s.1 s.2 hi
    | inr s => exact (exterior_frozen_degree n w d ell hell word closed c hc f P hm x s hi).trans (by decide)
  | inr s => rw [hi] at hx; exact False.elim (hx trivial)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
