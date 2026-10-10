import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellTarget
import OAI.Geometry.HyperbolicGroups.GraphGroupWalk

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace MacroGraph

lemma route_exists (v : Vertex) : Nonempty (graph.Walk (point 0) v) := by
  rcases v with ((i|l)|⟨⟩)
  · fin_cases i
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 2) (point 1) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 2) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 6) (point 3) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 2) (point 4) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 5) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 6) (point 6) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
  · fin_cases l
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 2) (line 0) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) SimpleGraph.Walk.nil)⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 2) from by simp only [graph]; decide) SimpleGraph.Walk.nil)⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 5) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 5) (line 3) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 2) (line 4) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 5) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 5) (line 5) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) SimpleGraph.Walk.nil)⟩
  · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 6) (point 3) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 3) (exceptional) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩

def route (v : Vertex) : graph.Walk (point 0) v := Classical.choice (route_exists v)

end MacroGraph
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma macro_darts (a : Top n w) {u : MacroGraph.Vertex}
    (p : MacroGraph.graph.Walk u u) (hp : p.IsCycle) :
    p.darts.map (fun e => macroStep n w a e.adj) = List.ofFn (topSide n w (a,⟨u,⟨p,hp⟩⟩)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hil : i < p.length := by simpa using hi
    have hid : i < p.darts.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map,List.getElem_ofFn,topSide]
    have he : p.darts[i]'hid = ⟨⟨p.getVert i,p.getVert (finRotate p.length ⟨i,hil⟩).val⟩,
        (MacroGraph.ofCycle p hp).adjacent ⟨i,hil⟩⟩ := by
      rw [SimpleGraph.Walk.darts_getElem_eq_getVert i hid]
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · rfl
      · change p.getVert (i+1) = p.getVert (finRotate p.length ⟨i,hil⟩).val
        have hn : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le_length
        have : NeZero p.length := ⟨by omega⟩
        rw [finRotate_apply,Fin.val_add]
        have hone : ((1 : Fin p.length) : ℕ) = 1 := by
          change 1 % p.length = 1
          exact Nat.mod_eq_of_lt (by have := hp.three_le_length; omega)
        rw [hone]
        by_cases hh : i+1 < p.length
        · rw [Nat.mod_eq_of_lt hh]
        · have he : i+1 = p.length := by simp only [List.length_map,SimpleGraph.Walk.length_darts] at hi; omega
          rw [he,Nat.mod_self,SimpleGraph.Walk.getVert_length,SimpleGraph.Walk.getVert_zero]
    exact congrArg (fun e : MacroGraph.graph.Dart => macroStep n w a e.adj) he

variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

def macroValue (a : Top n w) : MacroGraph.graph.Dart → H := fun e => c (macroStep n w a e.adj)
include hc in
lemma macroValue_symm (a : Top n w) (e : MacroGraph.graph.Dart) :
    macroValue n w c a e.symm = (macroValue n w c a e)⁻¹ := by
  exact (congrArg c (macroStep_reverse n w a e.adj)).trans (hc _)

include hcell in
lemma macro_cycle (a : Top n w) (u : MacroGraph.Vertex)
    (p : MacroGraph.graph.Walk u u) (hp : p.IsCycle) :
    GraphGroupWalk.eval (macroValue n w c a) p = 1 := by
  have hf := hcell (.inr (.inl (a,⟨u,⟨p,hp⟩⟩)))
  change (List.ofFn (fun i => c (topSide n w (a,⟨u,⟨p,hp⟩⟩) i))).prod = 1 at hf
  have hm := congrArg (fun l : List (Dart n w) => (l.map c).prod) (macro_darts n w a p hp)
  have hh : ((List.ofFn (topSide n w (a,⟨u,⟨p,hp⟩⟩))).map c).prod = 1 := by
    simpa only [List.map_ofFn,Function.comp_def] using hf
  change (List.map (fun e : MacroGraph.graph.Dart => c (macroStep n w a e.adj)) p.darts).prod = 1
  simpa only [List.map_map,Function.comp_def] using hm.trans hh

def macroPotential (a : Top n w) (v : MacroGraph.Vertex) : H :=
  GraphGroupWalk.eval (macroValue n w c a) (MacroGraph.route v)

include hc hcell in
lemma macroPotential_edge (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    macroPotential n w c a u * c (macroStep n w a h) = macroPotential n w c a v := by
  exact GraphGroupWalk.route_edge (macroValue n w c a) (macroValue_symm n w c hc a)
    (macro_cycle n w d c hcell a) (MacroGraph.route u) (MacroGraph.route v) h

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
