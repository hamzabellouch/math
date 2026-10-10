import Mathlib
import OAI.Geometry.HyperbolicGroups.MacroGroup
import OAI.Geometry.HyperbolicGroups.ConeFanGroup

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

def topPotential (a : Top n w) : MasterGraph.Vertex → H
  | .inl (.inl r) => macroPotential n w c a (MacroGraph.point (pointOfRepresentative r)) *
      radialValue n w c (slot n w a (pointOfRepresentative r)) ⟨.inl r,rfl⟩
  | .inl (.inr l) => macroPotential n w c a (MacroGraph.line l)
  | .inr _ => 1

include hc hcell in
lemma topPotential_edge (a : Top n w) (e : IncidenceTemplate.Edge) :
    topPotential n w c a (MasterGraph.source (.inl e)) * c (letterDart n w (a.val e)) =
    topPotential n w c a (MasterGraph.target (.inl e)) := by
  by_cases he : isLoose e
  · have he' : e = loose := Subtype.ext he
    subst e
    have hp := macroPotential_edge n w d c hc hcell a
      (show MacroGraph.Adjacent (MacroGraph.point 3) MacroGraph.exceptional from rfl)
    have hl := macroPotential_edge n w d c hc hcell a
      (show MacroGraph.Adjacent MacroGraph.exceptional (MacroGraph.line 4) from rfl)
    change (macroPotential n w c a (MacroGraph.point 3) *
      c (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,true)) * c (letterDart n w (a.val loose)) = _
    change macroPotential n w c a (MacroGraph.point 3) *
      c (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,true) = _ at hp
    rw [hp]
    exact hl
  · let i := pointOfRepresentative e.val.1
    have hf : e ∈ fan i := by simp [fan,i,he]
    have htri := fanTriangle_relation n w d c hc hcell ⟨slot n w a i,⟨e,hf⟩⟩
    have hadj : MacroGraph.Adjacent (MacroGraph.point i) (MacroGraph.line e.val.2) :=
      (edge_fan_vertices e i hf).2
    have hrad := macroPotential_edge n w d c hc hcell a hadj
    change (macroPotential n w c a (MacroGraph.point i) *
      radialValue n w c (slot n w a i) ⟨.inl e.val.1,rfl⟩) *
      c (letterDart n w (a.val e)) = macroPotential n w c a (MacroGraph.line e.val.2)
    rw [mul_assoc]
    change radialValue n w c (slot n w a i) ⟨.inl e.val.1,rfl⟩ *
      c (letterDart n w (a.val e)) =
      radialValue n w c (slot n w a i) ⟨.inr e.val.2,hadj⟩ at htri
    rw [htri]
    exact hrad

lemma row_extendCore_fan (l : Field → Alphabet n) (i : Fin 7) :
    TableModel.row rowSupport (extendCore n (fun e => l (.inl e))) (.inl i) =
    TableModel.row rowSupport l (.inl i) := by
  unfold TableModel.row
  apply congrArg (Sigma.mk _)
  funext f
  rcases f with ⟨e | s,h⟩
  · rfl
  · simp [rowSupport] at h

lemma row_extendCore_top (l : Field → Alphabet n) :
    TableModel.row rowSupport (extendCore n (fun e => l (.inl e))) (.inr (.inl ())) =
    TableModel.row rowSupport l (.inr (.inl ())) := by
  unfold TableModel.row
  apply congrArg (Sigma.mk _)
  funext f
  rcases f with ⟨e | s,h⟩
  · rfl
  · simp [rowSupport] at h

include hc hcell in
lemma top_relator_value (l : Field → Alphabet n)
    (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
    (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
    (v : MasterGraph.Vertex) (p : MasterGraph.Path v v) (core : p.IsCore) :
    p.eval l (c ∘ letterDart n w) = 1 := by
  let a : Top n w := ⟨fun e => l (.inl e),by
    constructor
    · simpa only [row_extendCore_top] using present
    · intro i; simpa only [row_extendCore_fan] using fans i⟩
  have hp : topPotential n w c a v * p.eval ((c ∘ letterDart n w) ∘ l) id =
      topPotential n w c a v := by
    apply p.eval_potential
    intro f hf
    obtain ⟨e,rfl⟩ := core f hf
    exact topPotential_edge n w d c hc hcell a e
  rw [MasterGraph.Path.eval_comp] at hp
  exact mul_left_cancel (hp.trans (mul_one _).symm)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
