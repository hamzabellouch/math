import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFrozenTarget

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual oriented macro edge in the indexed attaching polygon. -/
def topDart (a : TopPolygon n w) (i : Fin a.2.2.val.length) : MacroGraph.graph.Dart :=
  ⟨(a.2.2.val.getVert i.val,
    a.2.2.val.getVert ((finRotate a.2.2.val.length) i).val),
    (MacroGraph.ofCycle a.2.2.val a.2.2.property).adjacent i⟩

/-- Forget only the choice of simple circuit surrounding a top step.
Frozen fan/decorative cell identities and all their positions are retained. -/
def cellWalkStep : (boundary n w d).Side → WalkStep n w d
  | ⟨.inl a,b,i⟩ => .inr ⟨.inl a,b,i⟩
  | ⟨.inr (.inl a),b,i⟩ => .inl (a.1,if b then topDart n w a i else (topDart n w a i).symm)
  | ⟨.inr (.inr a),b,i⟩ => .inr ⟨.inr a,b,i⟩

lemma cellWalkStep_label (s : (boundary n w d).Side) :
    walkLabel n w d (cellWalkStep n w d s) = (boundary n w d).sideLabel s := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a)
  · rfl
  · cases b with
    | false => exact macroStep_reverse n w a.1 _
    | true => rfl
  · rfl

lemma cellWalkStep_kind (s : (boundary n w d).Side) :
    walkKind n w d (cellWalkStep n w d ((boundary n w d).next s)) =
      walkKind n w d (cellWalkStep n w d s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a) <;> rfl

lemma cellWalkStep_closed (s : (boundary n w d).Side) :
    walkFront n w d (cellWalkStep n w d ((boundary n w d).next s)) =
      walkBack n w d (cellWalkStep n w d s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a)
  · exact congrArg Sum.inr ((frozenBoundary n w d).next_start ⟨.inl a,b,i⟩)
  · cases b with
    | false =>
      change Sum.inl (a.1,a.2.2.val.getVert
        ((finRotate a.2.2.val.length) ((finRotate a.2.2.val.length)⁻¹ i)).val) =
          Sum.inl (a.1,a.2.2.val.getVert i.val)
      change Fin a.2.2.val.length at i
      rw [Perm.inv_def,Equiv.apply_symm_apply]
    | true => rfl
  · exact congrArg Sum.inr ((frozenBoundary n w d).next_start ⟨.inr a,b,i⟩)

lemma cellWalkStep_frozen_next (s : (boundary n w d).Side)
    (h : walkFree n w d (walkKind n w d (cellWalkStep n w d s)) = false) :
    cellWalkStep n w d ((boundary n w d).next s) =
      (Equiv.sumCongr (1 : Perm (Top n w × MacroGraph.graph.Dart)) (frozenBoundary n w d).next)
        (cellWalkStep n w d s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a)
  · rfl
  · cases h
  · rfl

lemma cellWalkStep_frozen_inj {s t : (boundary n w d).Side}
    (h : walkFree n w d (walkKind n w d (cellWalkStep n w d s)) = false)
    (he : cellWalkStep n w d s = cellWalkStep n w d t) : s = t := by
  rcases s with ⟨a,b,i⟩
  rcases t with ⟨a',b',i'⟩
  rcases a with a | (a | a)
  · rcases a' with a' | (a' | a')
    · have hh := Sum.inr.inj he
      have ha : a = a' := Sum.inl.inj (Sigma.mk.inj hh).1
      subst a'
      have hi := eq_of_heq (Sigma.mk.inj hh).2
      cases hi
      rfl
    · cases he
    · have hh := (Sigma.mk.inj (Sum.inr.inj he)).1
      cases hh
  · cases h
  · rcases a' with a' | (a' | a')
    · have hh := (Sigma.mk.inj (Sum.inr.inj he)).1
      cases hh
    · cases he
    · have hh := Sum.inr.inj he
      have ha : a = a' := Sum.inr.inj (Sigma.mk.inj hh).1
      subst a'
      have hi := eq_of_heq (Sigma.mk.inj hh).2
      cases hi
      rfl

variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (weight : Cell n w d → A)
universe u
variable (P : CellPicture.{u} (target n w d weight))

/-- Raw mixed pictures are now produced from actual indexed cellular pictures;
no simple/reduced/fan-link condition is assumed at this bridge. -/
def cellToWalk : WalkPicture.{u} (walkTarget n w d c hc f) where
  Dart := P.Dart
  pairing := P.pairing
  index := cellWalkStep n w d ∘ P.index
  closed := by
    intro x
    change walkFront n w d (cellWalkStep n w d (P.index (P.pairing.face x))) = _
    rw [P.mapped.commute]
    exact cellWalkStep_closed n w d _
  kind := by
    intro x
    change walkKind n w d (cellWalkStep n w d (P.index (P.pairing.face x))) = _
    rw [P.mapped.commute]
    exact cellWalkStep_kind n w d _
  paired := by
    intro x
    change walkLabel n w d (cellWalkStep n w d (P.index (P.pairing.edge x))) =
      rev n w (walkLabel n w d (cellWalkStep n w d (P.index x)))
    rw [cellWalkStep_label,cellWalkStep_label]
    exact P.respects.2 x
  genusZero := P.genusZero

lemma cellToWalk_frozen : (cellToWalk n w d c hc f weight P).FrozenMapped
    (walkFrozenTarget n w d c hc f) := by
  constructor
  · intro x
    change cellWalkStep n w d (P.index (P.pairing.face x.val)) = _
    exact (congrArg (cellWalkStep n w d) (P.mapped.commute x.val)).trans
      (cellWalkStep_frozen_next n w d _ x.property)
  · intro x y hxy he
    apply Subtype.ext
    apply P.mapped.injective
    · exact semiconj_perm_sameCycle (j := fun x : (cellToWalk n w d c hc f weight P).FrozenDart => (x.val : P.Dart))
        (t := P.pairing.face) (fun _ => rfl) hxy
    · exact cellWalkStep_frozen_inj n w d x.property he

end HyperbolicObstruction.ConeSkeleton
end

end OAI
