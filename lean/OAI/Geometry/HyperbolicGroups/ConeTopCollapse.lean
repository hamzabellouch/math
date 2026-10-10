import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeLetterCollapse
import OAI.Geometry.HyperbolicGroups.MacroGroup

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace CoreWordGraph
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph

lemma label_congr (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l k : Field → Alphabet n) (h : ∀ e ∈ S, l (.inl e) = k (.inl e)) (e : (graph S).Dart) :
    label S n l e = label S n k e := by
  unfold label stepLetter
  rw [MasterGraph.coreStep_field,h _ (core_edge_mem S e.adj)]

lemma word_congr (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l k : Field → Alphabet n) (h : ∀ e ∈ S, l (.inl e) = k (.inl e))
    {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    GraphWordFilling.word (label S n l) p = GraphWordFilling.word (label S n k) p := by
  unfold GraphWordFilling.word
  apply List.map_congr_left
  intro e he
  exact label_congr S n l k h e

end CoreWordGraph
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma slot_radial_word (a : Top n w) (i : Fin 7) (v : FanVertex i) :
    GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.val))
      ((CoreWordGraph.fanRoute i v).map (CoreWordGraph.inclusion (fan i))) =
      radialWord n w (slot n w a i) v := by
  rw [CoreWordGraph.inclusion_word]
  apply CoreWordGraph.word_congr
  intro e he
  simp [extendRow,slot,show (.inl e : Field) ∈ rowSupport (.inl i) from by simpa [rowSupport] using he]

def macroBase : MacroGraph.Vertex → CoreGeometry.Vertex
  | .inl (.inl i) => .inl (CoreWordGraph.base i)
  | .inl (.inr l) => .inr l
  | .inr _ => .inl 3

/-- Send apex i to its fixed actual fan base and expand radial edges by
fixed fan paths. The exceptional two-step incidence uses the genuine loose
letter, not a fictitious eighth fan. -/
def macroRoute {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    (CoreWordGraph.graph Finset.univ).Walk (macroBase u) (macroBase v) := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact (CoreWordGraph.fanRoute i ⟨.inr m,h⟩).map (CoreWordGraph.inclusion (fan i))
  · have hi : i = 3 := h
    subst i
    exact (CoreWordGraph.fanRoute 3 ⟨.inl 3,by decide⟩).map (CoreWordGraph.inclusion (fan 3))
  · exact ((CoreWordGraph.fanRoute j ⟨.inr l,h⟩).map (CoreWordGraph.inclusion (fan j))).reverse
  · exact h.elim
  · have hl : l = 4 := h
    subst l
    exact .cons (show (CoreWordGraph.graph Finset.univ).Adj (.inr 4) (.inl 3) from
      ⟨loose,rfl,Finset.mem_univ _⟩) .nil
  · have hj : j = 3 := h
    subst j
    exact ((CoreWordGraph.fanRoute 3 ⟨.inl 3,by decide⟩).map (CoreWordGraph.inclusion (fan 3))).reverse
  · have hm : m = 4 := h
    subst m
    exact .cons (show (CoreWordGraph.graph Finset.univ).Adj (.inl 3) (.inr 4) from
      ⟨loose,rfl,Finset.mem_univ _⟩) .nil
  · exact h.elim

lemma macroRoute_length {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    (macroRoute h).length ≤ 2 := by
  have mapped_length (i : Fin 7) (v : FanVertex i) :
      ((CoreWordGraph.fanRoute i v).map (CoreWordGraph.inclusion (fan i))).length ≤ 2 :=
    (Walk.length_map (CoreWordGraph.inclusion (fan i)) (CoreWordGraph.fanRoute i v)).trans_le
      (CoreWordGraph.fanRoute_length i v)
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact mapped_length i ⟨.inr m, h⟩
  · have hi : i = 3 := h; subst i
    exact mapped_length 3 ⟨.inl 3, by decide⟩
  · exact (Walk.length_reverse _).trans_le (mapped_length j ⟨.inr l, h⟩)
  · exact h.elim
  · have hl : l = 4 := h; subst l
    change (1 : ℕ) ≤ 2
    decide
  · have hj : j = 3 := h; subst j
    exact (Walk.length_reverse _).trans_le (mapped_length 3 ⟨.inl 3, by decide⟩)
  · have hm : m = 4 := h; subst m
    change (1 : ℕ) ≤ 2
    decide
  · exact h.elim

lemma macroRoute_word (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.val)) (macroRoute h) =
      collapse n w (macroStep n w a h) := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact slot_radial_word n w a i ⟨.inr m,h⟩
  · have hi : i = 3 := h; subst i
    exact slot_radial_word n w a 3 ⟨.inl 3,by decide⟩
  · change GraphWordFilling.word _ ((CoreWordGraph.fanRoute j ⟨.inr l,h⟩).map _).reverse = _
    rw [GraphWordFilling.word_reverse _ (CoreWordGraph.label_rev _ _ _),slot_radial_word]
    rfl
  · exact h.elim
  · have hl : l = 4 := h; subst l
    change [inverseLetter n (a.val loose)] = _
    rfl
  · have hj : j = 3 := h; subst j
    change GraphWordFilling.word _ ((CoreWordGraph.fanRoute 3 ⟨.inl 3,by decide⟩).map _).reverse = _
    rw [GraphWordFilling.word_reverse _ (CoreWordGraph.label_rev _ _ _),slot_radial_word]
    rfl
  · have hm : m = 4 := h; subst m
    rfl
  · exact h.elim

def topCollapsedWalk (a : TopPolygon n w) :
    (CoreWordGraph.graph Finset.univ).Walk (macroBase a.2.1) (macroBase a.2.1) :=
  GraphWordFilling.expand macroBase (fun {_ _} h => macroRoute h) a.2.2.val

lemma topCollapsedWalk_length (a : TopPolygon n w) : (topCollapsedWalk n w a).length ≤ 30 := by
  have hl := GraphWordFilling.expand_length macroBase (fun {_ _} h => macroRoute h)
    2 (fun {_ _} h => macroRoute_length h) a.2.2.val
  have hp := MacroGraph.cycle_perimeter a.2.2.val a.2.2.property
  exact hl.trans (by omega)

lemma topCollapsedWalk_word (a : TopPolygon n w) :
    GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.1.val))
      (topCollapsedWalk n w a) = collapsedBoundary n w d (.inr (.inl a)) := by
  rw [topCollapsedWalk,GraphWordFilling.expand_word]
  change _ = (List.ofFn (topSide n w a)).flatMap (collapse n w)
  rw [← macro_darts n w a.1 a.2.2.val a.2.2.property,List.flatMap_map]
  apply List.flatMap_congr
  intro e he
  exact macroRoute_word n w a.1 e.adj

/-- Every actual simple top polygon collapses to a core closed walk of length
at most thirty, and hence to at most thirty exact finite-presentation faces. -/
theorem top_collapse_filling (a : TopPolygon n w) :
    ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
      (collapsedBoundary n w d (.inr (.inl a))) [] k := by
  obtain ⟨k,hk,hh⟩ := GraphWordFilling.closed_filling
    (CoreWordGraph.label Finset.univ n (extendCore n a.1.val)) (CoreWordGraph.label_rev _ _ _)
    (SimpleWordRelator n w d)
    (fun v p h => SimpleWordRelator.top (extendCore n a.1.val) a.1.property.1 a.1.property.2 v p h)
    (topCollapsedWalk n w a)
  exact ⟨k,hk.trans (topCollapsedWalk_length n w a),by rw [topCollapsedWalk_word n w d a] at hh; exact hh⟩

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
