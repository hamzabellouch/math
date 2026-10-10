import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeSkeleton
import OAI.Geometry.HyperbolicGroups.MacroCertificate

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

abbrev CoreRow := IncidenceTemplate.Edge → Alphabet n

def extendCore (a : CoreRow n) : Field → Alphabet n
  | .inl e => a e
  | .inr _ => (0,true)

/-- Only the 32 actual top fields index a top occurrence. Decorations are NOT
extra coordinates indexing redundant copies of a top cone. -/
abbrev Top := {a : CoreRow n //
  w (TableModel.row rowSupport (extendCore n a) (.inr (.inl ()))) = true ∧
  ∀ i : Fin 7, w (TableModel.row rowSupport (extendCore n a) (.inl i)) = true}

def slot (a : Top n w) (i : Fin 7) : Fan n w :=
  ⟨⟨i,fun f => extendCore n a.val f.val⟩,a.property.2 i⟩

lemma slot_type (a : Top n w) (i : Fin 7) : (slot n w a i).val.1 = i := rfl

lemma top_row_injective : Function.Injective
    (fun a : CoreRow n => TableModel.row rowSupport (extendCore n a) (.inr (.inl ()))) := by
  intro a b he
  funext e
  have hh := Sigma.mk.inj he
  have hh' : (fun f : rowSupport (.inr (.inl ())) => extendCore n a f.val) =
      (fun f : rowSupport (.inr (.inl ())) => extendCore n b f.val) := eq_of_heq hh.2
  exact congrFun hh' ⟨.inl e,by simp [rowSupport]⟩

def letterDart (a : Alphabet n) : Dart n w := (.inl a.1,a.2)

lemma rev_rev (l : Dart n w) : rev n w (rev n w l) = l := by
  rcases l with ⟨e,b⟩; cases b <;> rfl

lemma rev_letter (a : Alphabet n) : rev n w (letterDart n w a) =
    letterDart n w (inverseLetter n a) := rfl

lemma start_letter (a : Alphabet n) : start n w (letterDart n w a) = .inl () := by
  rcases a with ⟨e,b⟩; cases b <;> rfl

def macroVertex (a : Top n w) : MacroGraph.Vertex → Vertex n w
  | .inl (.inl i) => .inr (slot n w a i)
  | _ => .inl ()

def loose : IncidenceTemplate.Edge := ⟨(3,4),by decide⟩

/-- The literal map of the subdivided incidence graph from source02:72--79.
The exceptional two-edge path is radial X_D followed by the loose letter. -/
def macroStep (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) : Dart n w := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact (.inr ⟨slot n w a i,⟨.inr m,h⟩⟩,true)
  · have hi : i = 3 := h
    subst i
    exact (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,true)
  · exact (.inr ⟨slot n w a j,⟨.inr l,h⟩⟩,false)
  · exact h.elim
  · exact rev n w (letterDart n w (a.val loose))
  · have hj : j = 3 := h
    subst j
    exact (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,false)
  · exact letterDart n w (a.val loose)
  · exact h.elim

lemma macroStep_start (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    start n w (macroStep n w a h) = macroVertex n w a u := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · rfl
  · have hi : i = 3 := h; subst i; rfl
  · rfl
  · exact h.elim
  · exact start_letter n w (inverseLetter n (a.val loose))
  · have hj : j = 3 := h; subst j; rfl
  · exact start_letter n w _
  · exact h.elim

lemma macroStep_reverse (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    macroStep n w a (MacroGraph.adjacent_symm h) = rev n w (macroStep n w a h) := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · rfl
  · have hi : i = 3 := h; subst i; rfl
  · rfl
  · exact h.elim
  · exact (rev_rev n w _).symm
  · have hj : j = 3 := h; subst j; rfl
  · rfl
  · exact h.elim

lemma macroStep_end (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    start n w (rev n w (macroStep n w a h)) = macroVertex n w a v := by
  rw [← macroStep_reverse]
  exact macroStep_start n w a _

/-- Each fan triangle retains its original edge field and BOTH distinct
radial ports, independently of repetitions in the assigned generator row. -/
abbrev FanTriangle := Σ b : Fan n w, {e : IncidenceTemplate.Edge // e ∈ fan b.val.1}

def fanLetter (f : FanTriangle n w) : Alphabet n :=
  f.1.val.2 ⟨.inl f.2.val,by simp [rowSupport]⟩

def fanLeft (f : FanTriangle n w) : FanVertex f.1.val.1 :=
  ⟨.inl f.2.val.val.1,(edge_fan_vertices _ _ f.2.property).1⟩
def fanRight (f : FanTriangle n w) : FanVertex f.1.val.1 :=
  ⟨.inr f.2.val.val.2,(edge_fan_vertices _ _ f.2.property).2⟩

def fanSide (f : FanTriangle n w) : Fin 3 → Dart n w :=
  ![(.inr ⟨f.1,fanLeft n w f⟩,true),letterDart n w (fanLetter n w f),
    (.inr ⟨f.1,fanRight n w f⟩,false)]

lemma fanSide_closed (f : FanTriangle n w) (i : Fin 3) :
    start n w (fanSide n w f (finRotate 3 i)) = start n w (rev n w (fanSide n w f i)) := by
  fin_cases i
  · exact start_letter n w _
  · exact (start_letter n w (inverseLetter n (fanLetter n w f))).symm
  · rfl

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
