import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellTarget
import OAI.Geometry.HyperbolicGroups.FanRoute
import OAI.Geometry.HyperbolicGroups.GraphSubstitution
import OAI.Geometry.HyperbolicGroups.SimpleLetterPresentation

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def radialWord (f : Fan n w) (v : FanVertex f.val.1) : List (Alphabet n) :=
  GraphWordFilling.word (CoreWordGraph.label (fan f.val.1) n (extendRow n (.inl f.val.1) f.val.2))
    (CoreWordGraph.fanRoute f.val.1 v)

/-- Literal radial-path collapse of the actual cone one-skeleton. It fixes
all letter edges, and does not identify two indexed radial positions. -/
def collapse : Dart n w → List (Alphabet n)
  | (.inl a,b) => [(a,b)]
  | (.inr ⟨f,v⟩,true) => radialWord n w f v
  | (.inr ⟨f,v⟩,false) => FreeGroup.invRev (radialWord n w f v)

lemma collapse_rev (e : Dart n w) : collapse n w (rev n w e) = FreeGroup.invRev (collapse n w e) := by
  rcases e with ⟨a|⟨f,v⟩,b⟩ <;> cases b <;>
    simp only [collapse,rev,Bool.not_false,Bool.not_true,FreeGroup.invRev_invRev] <;> rfl

lemma collapse_letter (a : Alphabet n) : collapse n w (letterDart n w a) = [a] := rfl

lemma collapse_length (e : Dart n w) : (collapse n w e).length ≤ 2 := by
  rcases e with ⟨a|⟨f,v⟩,b⟩ <;> cases b
  · simp [collapse]
  · simp [collapse]
  · simpa only [collapse,FreeGroup.invRev_length,radialWord,GraphWordFilling.word_length] using
      CoreWordGraph.fanRoute_length f.val.1 v
  · simpa only [collapse,radialWord,GraphWordFilling.word_length] using
      CoreWordGraph.fanRoute_length f.val.1 v

def collapsedBoundary (c : Cell n w d) : List (Alphabet n) :=
  (List.ofFn (side n w d c)).flatMap (collapse n w)

lemma fan_edge_adj (f : FanTriangle n w) :
    (CoreWordGraph.graph (fan f.1.val.1)).Adj (fanLeft n w f).val (fanRight n w f).val :=
  ⟨f.2.val,rfl,f.2.property⟩

lemma fan_edge_label (f : FanTriangle n w) :
    CoreWordGraph.label (fan f.1.val.1) n (extendRow n (.inl f.1.val.1) f.1.val.2)
      ⟨((fanLeft n w f).val,(fanRight n w f).val),fan_edge_adj n w f⟩ = fanLetter n w f := by
  change extendRow n (.inl f.1.val.1) f.1.val.2 (.inl f.2.val) = _
  simp [extendRow,fanLetter,show (.inl f.2.val : Field) ∈ rowSupport (.inl f.1.val.1) from
    by simp [rowSupport]]

def fanCollapsedWalk (f : FanTriangle n w) :
    (CoreWordGraph.graph (fan f.1.val.1)).Walk (.inl (CoreWordGraph.base f.1.val.1))
      (.inl (CoreWordGraph.base f.1.val.1)) :=
  (CoreWordGraph.fanRoute f.1.val.1 (fanLeft n w f)).append
    (.cons (fan_edge_adj n w f) (CoreWordGraph.fanRoute f.1.val.1 (fanRight n w f)).reverse)

lemma fanCollapsedWalk_length (f : FanTriangle n w) : (fanCollapsedWalk n w f).length ≤ 5 := by
  have hl := CoreWordGraph.fanRoute_length f.1.val.1 (fanLeft n w f)
  have hr := CoreWordGraph.fanRoute_length f.1.val.1 (fanRight n w f)
  simp only [fanCollapsedWalk,Walk.length_append,Walk.length_cons,Walk.length_reverse]
  omega

lemma fanCollapsedWalk_word (f : FanTriangle n w) :
    GraphWordFilling.word (CoreWordGraph.label (fan f.1.val.1) n (extendRow n (.inl f.1.val.1) f.1.val.2))
      (fanCollapsedWalk n w f) = collapsedBoundary n w d (.inl f) := by
  rw [fanCollapsedWalk,GraphWordFilling.word_append,GraphWordFilling.word_cons,
    GraphWordFilling.word_reverse _ (CoreWordGraph.label_rev _ _ _),fan_edge_label]
  change _ = radialWord n w f.1 (fanLeft n w f) ++
    ([fanLetter n w f] ++ (FreeGroup.invRev (radialWord n w f.1 (fanRight n w f)) ++ []))
  simp only [List.append_nil, List.singleton_append, radialWord]

/-- The actual source fan-triangle substitution, including backtracking fan
paths, needs no more than five faces of the finite simple-cycle presentation. -/
theorem fan_collapse_filling (f : FanTriangle n w) :
    ∃ a ≤ 5, WordPictures.Homotopy (SimpleWordRelator n w d)
      (collapsedBoundary n w d (.inl f)) [] a := by
  let l := extendRow n (.inl f.1.val.1) f.1.val.2
  have hp : w (TableModel.row rowSupport l (.inl f.1.val.1)) = true := by
    simpa only [l,row_extend] using f.1.property
  obtain ⟨a,ha,hh⟩ := GraphWordFilling.closed_filling
    (CoreWordGraph.label (fan f.1.val.1) n l) (CoreWordGraph.label_rev _ _ _)
    (SimpleWordRelator n w d) (fun v p h => SimpleWordRelator.fan l f.1.val.1 hp v p h)
    (fanCollapsedWalk n w f)
  refine ⟨a,ha.trans (fanCollapsedWalk_length n w f),?_⟩
  dsimp only [l] at hh
  rw [fanCollapsedWalk_word n w d f] at hh
  exact hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
