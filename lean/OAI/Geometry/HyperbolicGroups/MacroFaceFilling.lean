import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList
import OAI.Geometry.HyperbolicGroups.BoundaryGraphWalk
import OAI.Geometry.HyperbolicGroups.ConeTopCollapse

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The source's fifteen-side bound read directly from the actual cyclic
macro-face parametrization, without identifying random letters. -/
lemma macro_parametrization_card (p : Perm D) (j : D → MacroGraph.graph.Dart)
    (hc : ∀ x, (j (p x)).fst = (j x).snd)
    (hi : Function.Injective (fun x => (j x).fst))
    (hb : ∀ x, p (p x) ≠ x) : Fintype.card D ≤ 15 := by
  let b := (Fintype.equivFin D).symm
  let Q : MacroGraph.Polygon := {
    n := Fintype.card D
    vertex := fun i => (j (b i)).fst
    next := b.trans (p.trans b.symm)
    injective := hi.comp b.injective
    adjacent := by
      intro i
      change MacroGraph.Adjacent (j (b i)).fst (j (b (b.symm (p (b i))))).fst
      rw [b.apply_symm_apply,hc]
      exact (j (b i)).adj
    no_backtrack := by
      intro i he
      have hh := congrArg b he
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hh
      exact hb (b i) hh }
  exact Q.perimeter_le

/-- A literal bounded free macro face has a cost at most thirty in the exact
finite simple-cycle presentation, via genuine core-graph routes. -/
theorem macro_boundary_filling (a : Top n w) (p : Perm D) (j : D → MacroGraph.graph.Dart)
    (hc : ∀ x, (j (p x)).fst = (j x).snd)
    (hi : Function.Injective (fun x => (j x).fst))
    (hb : ∀ x, p (p x) ≠ x)
    (xs : List D) (hx : IsBoundary p xs) (hne : xs ≠ []) :
    ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
      ((xs.map (fun x => macroStep n w a (j x).adj)).flatMap (collapse n w)) [] k := by
  obtain ⟨v,q,hq⟩ := hx.graph_closed_walk j (fun x _ => hc x) hne
  have hl : q.length ≤ 15 := by
    rw [← SimpleGraph.Walk.length_darts,hq,List.length_map]
    exact (List.Nodup.length_le_card hx.nodup).trans (macro_parametrization_card p j hc hi hb)
  let q' := GraphWordFilling.expand macroBase (fun {_ _} h => macroRoute h) q
  have hlen : q'.length ≤ 30 := by
    have h := GraphWordFilling.expand_length macroBase (fun {_ _} h => macroRoute h)
      2 (fun {_ _} h => macroRoute_length h) q
    exact h.trans (by omega)
  obtain ⟨k,hk,hh⟩ := GraphWordFilling.closed_filling
    (CoreWordGraph.label Finset.univ n (extendCore n a.val)) (CoreWordGraph.label_rev _ _ _)
    (SimpleWordRelator n w d)
    (fun v p h => SimpleWordRelator.top (extendCore n a.val) a.property.1 a.property.2 v p h) q'
  refine ⟨k,hk.trans hlen,?_⟩
  have hword : GraphWordFilling.word (CoreWordGraph.label Finset.univ n (extendCore n a.val)) q' =
      ((xs.map (fun x => macroStep n w a (j x).adj)).flatMap (collapse n w)) := by
    simp only [q',GraphWordFilling.expand_word,hq,List.flatMap_map]
    apply List.flatMap_congr
    intro x hx
    exact macroRoute_word n w a (j x).adj
  rwa [hword] at hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
