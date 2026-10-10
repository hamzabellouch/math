import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryEnumeration
import OAI.Geometry.HyperbolicGroups.MacroFaceFilling
import OAI.Geometry.HyperbolicGroups.ConeExteriorWalk
import OAI.Geometry.HyperbolicGroups.ConeCellCollapse
import OAI.Geometry.HyperbolicGroups.PolygonFilling

namespace OAI

noncomputable section

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

lemma exterior_same_top {x y : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (.inl (a,e))) (h : P.pairing.face.SameCycle x y) :
    ∃ e', P.index y = .inl (.inl (a,e')) := by
  have hk := sameCycle_one.mp (semiconj_perm_sameCycle
    (t := (1 : Perm (WalkKind n w d ⊕ Unit))) P.kind h)
  dsimp only [Function.comp_apply] at hk
  rw [hx] at hk
  cases hy : P.index y with
  | inl s =>
    cases s with
    | inl s =>
      rw [hy] at hk
      have hs : a = s.1 := Sum.inl.inj (Sum.inl.inj hk)
      exact ⟨s.2,by rw [hs]⟩
    | inr s => rw [hy] at hk; cases hk
  | inr s => rw [hy] at hk; cases hk

/-- Local source03 cost for an ACTUAL free face in a protected normal disk.
Simplicity is read in the template, never in the random bouquet labels. -/
theorem exterior_top_filling (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart)
    (hx : P.index x = .inl (.inl (a,e))) :
    ∃ ys : List P.Dart, IsBoundary P.pairing.face ys ∧ x ∈ ys ∧
      ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
        ((ys.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index)).flatMap
          (collapse n w)) [] k := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  have hfree (y : I) : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  have hclose (y : I) : (j (q y)).fst = (j y).snd := by
    have h := P.closed y.val
    change (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (P.index (q y).val) = (exteriorWalkTarget n w d ell hell word closed c hc f).back
        (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj h))
  have hinj : Function.Injective (fun y : I => (j y).fst) := by
    intro i k hik
    apply Subtype.ext
    apply P.simple_front hs (hfree i) (i.property.symm.trans k.property)
    rw [hj,hj]
    exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl hik))
  have hnobig : ∀ y, q (q y) ≠ y := by
    intro y he
    exact hb y.val (hfree y) (congrArg Subtype.val he)
  obtain ⟨zs,hzs,hm⟩ := exists_boundary q (⟨x,SameCycle.rfl⟩ : I)
  obtain ⟨k,hk,hfill⟩ := macro_boundary_filling n w d a q j hclose hinj hnobig zs hzs
    (by intro he; rw [he] at hm; cases hm)
  refine ⟨zs.map Subtype.val,hzs.map Subtype.val Subtype.val_injective (fun _ => rfl),
    List.mem_map_of_mem hm,k,hk,?_⟩
  convert hfill using 1
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro y hy
  dsimp only [Function.comp_apply]
  rw [hj]
  rfl

/-- Frozen triangles and decorations retain the complete indexed attaching
polygon. Pulling that literal boundary back preserves its true local cost. -/
theorem exterior_frozen_filling
    (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
    (x : P.Dart) (s : (frozenBoundary n w d).Side)
    (hx : P.index x = .inl (.inr s)) :
    ∃ ys : List P.Dart, IsBoundary P.pairing.face ys ∧ x ∈ ys ∧
      ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
        ((ys.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index)).flatMap
          (collapse n w)) [] k := by
  obtain ⟨ys,hys,hmem,hrel⟩ := (frozenBoundary n w d).relator_boundary rfl s.1
    (R := Set.range (frozenBoundary n w d).attachingWord) ⟨s.1,rfl⟩ s.2.1 s.2.2
  have hlocal : ∀ r ∈ Set.range (frozenBoundary n w d).attachingWord,
      ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
        (r.flatMap (collapse n w)) [] k := by
    rintro r ⟨z,rfl⟩
    exact cell_collapse_filling n w d (frozenCell n w d z)
  obtain ⟨k,hk,hfill⟩ := hrel.filling.substitute (collapse n w)
    (fun e => collapse_rev n w e) hlocal
  have hxF : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index x)) = false := by
    rw [hx]; rfl
  let j : (frozenBoundary n w d).Side →
      WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell word closed :=
    fun z => .inl (.inr z)
  have hj : Function.Injective j := Sum.inl_injective.comp Sum.inr_injective
  have hys' : IsBoundary (exteriorWalkFrozen n w d ell hell word closed c hc f).next
      (ys.map j) := hys.map j hj (fun _ => rfl)
  obtain ⟨zs,hzs,hzm,hmap⟩ := hm.pullback_boundary (⟨x,hxF⟩ : P.FrozenDart) hys'
    (by change P.index x ∈ ys.map j; rw [hx]; exact List.mem_map_of_mem hmem)
  have hlabel : (zs.map Subtype.val).map
        ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index) =
      ys.map (frozenBoundary n w d).sideLabel := by
    have hh := congrArg
      (List.map (exteriorWalkTarget n w d ell hell word closed c hc f).label) hmap
    simp only [List.map_map] at hh ⊢
    convert hh using 1
    congr 1
    apply List.map_congr_left
    intro z hz
    rfl
  refine ⟨zs.map Subtype.val,hzs.map Subtype.val Subtype.val_injective (fun _ => rfl),
    List.mem_map_of_mem hzm,k,by simpa using hk,?_⟩
  rw [hlabel]
  exact hfill

end HyperbolicObstruction.ConeSkeleton
end

end OAI
