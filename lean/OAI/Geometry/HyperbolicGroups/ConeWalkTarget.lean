import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellTarget
import OAI.Geometry.HyperbolicGroups.WalkCell

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Actual non-top cells; these faces must not be split during macro surgery. -/
abbrev FrozenCell := FanTriangle n w ⊕ (Square n w ⊕ Six n d)

def frozenCell : FrozenCell n w d → Cell n w d
  | .inl f => .inl f
  | .inr e => .inr (.inr e)

def frozenBoundary : PolygonTarget.Boundary (FrozenCell n w d) (Dart n w) (Vertex n w) where
  size c := size n w d (frozenCell n w d c)
  positive cell := size_positive n w d (frozenCell n w d cell)
  label c := side n w d (frozenCell n w d c)
  start := start n w
  rev := rev n w
  inv := rev_rev n w
  closed cell := side_closed n w d (frozenCell n w d cell)

abbrev WalkStep := (Top n w × MacroGraph.graph.Dart) ⊕ (frozenBoundary n w d).Side
abbrev WalkKind := Top n w ⊕ FrozenCell n w d
abbrev WalkVertex := (Top n w × MacroGraph.Vertex) ⊕ Vertex n w

def walkKind : WalkStep n w d → WalkKind n w d
  | .inl s => .inl s.1
  | .inr s => .inr s.1

def walkFree : WalkKind n w d → Bool
  | .inl _ => true
  | .inr _ => false

def walkFront : WalkStep n w d → WalkVertex n w
  | .inl s => .inl (s.1,s.2.fst)
  | .inr s => .inr (start n w ((frozenBoundary n w d).sideLabel s))

def walkBack : WalkStep n w d → WalkVertex n w
  | .inl s => .inl (s.1,s.2.snd)
  | .inr s => .inr (start n w (rev n w ((frozenBoundary n w d).sideLabel s)))

def walkVertex : WalkVertex n w → Vertex n w
  | .inl s => macroVertex n w s.1 s.2
  | .inr v => v

def walkLabel : WalkStep n w d → Dart n w
  | .inl s => macroStep n w s.1 s.2.adj
  | .inr s => (frozenBoundary n w d).sideLabel s

def walkOpposite : WalkStep n w d → WalkStep n w d
  | .inl s => .inl (s.1,s.2.symm)
  | .inr s => .inr ((frozenBoundary n w d).opposite s)

lemma walkOpposite_kind (s : WalkStep n w d) :
    walkKind n w d (walkOpposite n w d s) = walkKind n w d s := by
  cases s <;> rfl

lemma walkOpposite_label (s : WalkStep n w d) :
    walkLabel n w d (walkOpposite n w d s) = rev n w (walkLabel n w d s) := by
  rcases s with s | s
  · exact macroStep_reverse n w s.1 s.2.adj
  · exact (frozenBoundary n w d).edge_opposite s

lemma walkOpposite_front (s : WalkStep n w d) :
    walkFront n w d (walkOpposite n w d s) = walkBack n w d s := by
  rcases s with s | s
  · rfl
  · change Sum.inr (start n w ((frozenBoundary n w d).sideLabel
        ((frozenBoundary n w d).opposite s))) = _
    rw [(frozenBoundary n w d).edge_opposite]; rfl

lemma walkOpposite_back (s : WalkStep n w d) :
    walkBack n w d (walkOpposite n w d s) = walkFront n w d s := by
  rcases s with s | s
  · rfl
  · change Sum.inr (start n w (rev n w ((frozenBoundary n w d).sideLabel
        ((frozenBoundary n w d).opposite s)))) = _
    rw [(frozenBoundary n w d).edge_opposite]
    change Sum.inr (start n w (rev n w (rev n w _))) = _
    rw [rev_rev]; rfl

lemma walk_loopless (s : WalkStep n w d) (hs : walkFree n w d (walkKind n w d s) = true) :
    walkFront n w d s ≠ walkBack n w d s := by
  rcases s with s | s
  · intro he
    exact s.2.fst_ne_snd (congrArg Prod.snd (Sum.inl.inj he))
  · cases hs

lemma walk_simple (s t : WalkStep n w d) (hs : walkFree n w d (walkKind n w d s) = true)
    (hk : walkKind n w d s = walkKind n w d t)
    (hf : walkFront n w d s = walkFront n w d t)
    (hb : walkBack n w d s = walkBack n w d t) : s = t := by
  rcases s with s | s
  · rcases t with t | t
    · have hf' : s.2.fst = t.2.fst :=
        congrArg (fun q : Top n w × MacroGraph.Vertex => q.2) (Sum.inl.inj hf)
      have hb' : s.2.snd = t.2.snd :=
        congrArg (fun q : Top n w × MacroGraph.Vertex => q.2) (Sum.inl.inj hb)
      exact congrArg Sum.inl (Prod.ext (Sum.inl.inj hk)
        (SimpleGraph.Dart.ext s.2 t.2 (Prod.ext hf' hb')))
    · cases hk
  · cases hs

variable {A : Type*} [AddCommGroup A]

/-- A frozen oriented face contributes its cellular coefficient once, at its
zero-th POSITION, not once per side. Top steps contribute their individually
indexed oriented elementary cone triangles. -/
def walkWeight (c : Top n w → MacroGraph.graph.Dart → A) (f : FrozenCell n w d → A) :
    WalkStep n w d → A
  | .inl s => c s.1 s.2
  | .inr s => if s.2.2.val = 0 then (frozenBoundary n w d).weight f s else 0

lemma walkWeight_opposite (c : Top n w → MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A) (s : WalkStep n w d) :
    walkWeight n w d c f s + walkWeight n w d c f (walkOpposite n w d s) = 0 := by
  rcases s with s | ⟨s,b,i⟩
  · change c s.1 s.2 + c s.1 s.2.symm = 0
    rw [hc,add_neg_cancel]
  · by_cases hi : i.val = 0 <;> cases b <;> simp [walkWeight,walkOpposite,PolygonTarget.Boundary.opposite,
      PolygonTarget.Boundary.weight,hi]

/-- Literal target for the actual top occurrences and their subdivided macro
edges. No simple-cycle or normal-picture assertion is included in this data.
In particular two DISTINCT top polygons using a common indexed cone side are
recognized as cancellable. -/
def walkTarget (c : Top n w → MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A) :
    WalkCellTarget (WalkStep n w d) (WalkKind n w d) (WalkVertex n w)
      (Dart n w) (Vertex n w) A where
  kind := walkKind n w d
  free := walkFree n w d
  front := walkFront n w d
  back := walkBack n w d
  vertex := walkVertex n w
  label := walkLabel n w d
  start := start n w
  rev := rev n w
  rev_rev := rev_rev n w
  front_label := by
    rintro (s | s)
    · exact macroStep_start n w s.1 s.2.adj
    · rfl
  back_label := by
    rintro (s | s)
    · exact macroStep_end n w s.1 s.2.adj
    · rfl
  opposite := walkOpposite n w d
  opposite_kind := walkOpposite_kind n w d
  opposite_front := walkOpposite_front n w d
  opposite_back := walkOpposite_back n w d
  opposite_label := walkOpposite_label n w d
  loopless := walk_loopless n w d
  simple := walk_simple n w d
  weight := walkWeight n w d c f
  opposite_weight := fun s _ => walkWeight_opposite n w d c hc f s

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
