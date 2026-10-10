import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeWalkTarget
import OAI.Geometry.HyperbolicGroups.FullWalkNormal

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def isLetter (l : Dart n w) : Bool := match l.1 with | .inl _ => true | .inr _ => false

/-- Indexed positions, NOT generator labels. Two fields carrying an equal
numerical letter remain distinct positions. -/
abbrev RawPosition := Top n w ⊕ (FanTriangle n w ⊕ ((Square n w × Fin 4) ⊕ (Six n d × Fin 6)))

def rawPosition : WalkStep n w d → RawPosition n w d
  | .inl s => .inl s.1
  | .inr ⟨.inl g,_,_⟩ => .inr (.inl g)
  | .inr ⟨.inr (.inl s),_,i⟩ => .inr (.inr (.inl (s,i)))
  | .inr ⟨.inr (.inr s),_,i⟩ => .inr (.inr (.inr (s,i)))

def looseMacro : MacroGraph.graph.Dart :=
  ⟨(MacroGraph.exceptional,MacroGraph.line 4),rfl⟩

def rawRepresentative : RawPosition n w d → WalkStep n w d
  | .inl a => .inl (a,looseMacro)
  | .inr (.inl g) => .inr ⟨.inl g,true,(1 : Fin 3)⟩
  | .inr (.inr (.inl p)) => .inr ⟨.inr (.inl p.1),true,p.2⟩
  | .inr (.inr (.inr p)) => .inr ⟨.inr (.inr p.1),true,p.2⟩

lemma macro_letter_cases (a : Top n w) (e : MacroGraph.graph.Dart)
    (hr : isLetter n w (macroStep n w a e.adj) = true) :
    e = looseMacro ∨ e = looseMacro.symm := by
  rcases e with ⟨⟨u,v⟩,h⟩
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · cases h
  · cases hr
  · have hi : i = 3 := h
    subst i
    cases hr
  · cases hr
  · cases h
  · have hl : l = 4 := h
    subst l
    exact Or.inr rfl
  · have hj : j = 3 := h
    subst j
    cases hr
  · have hm : m = 4 := h
    subst m
    exact Or.inl rfl
  · cases h

lemma fan_letter_index (g : FanTriangle n w) (o : Bool) (i : Fin 3)
    (hr : isLetter n w (walkLabel n w d (.inr ⟨.inl g,o,i⟩)) = true) : i = 1 := by
  cases o <;> fin_cases i
  · cases hr
  · rfl
  · cases hr
  · cases hr
  · rfl
  · cases hr

lemma walkOpposite_twice (s : WalkStep n w d) :
    walkOpposite n w d (walkOpposite n w d s) = s := by
  rcases s with s | ⟨c,o,i⟩
  · rfl
  · cases o <;> rfl

lemma raw_step_cases (s : WalkStep n w d) (hr : isLetter n w (walkLabel n w d s) = true) :
    s = rawRepresentative n w d (rawPosition n w d s) ∨
      s = walkOpposite n w d (rawRepresentative n w d (rawPosition n w d s)) := by
  rcases s with ⟨a,e⟩ | ⟨g,o,i⟩
  · rcases macro_letter_cases n w a e hr with he | he
    · subst e; exact Or.inl rfl
    · subst e; exact Or.inr rfl
  · rcases g with g | (q | q)
    · have hi := fan_letter_index n w d g o i hr
      subst i
      cases o
      · exact Or.inr rfl
      · exact Or.inl rfl
    · cases o
      · exact Or.inr rfl
      · exact Or.inl rfl
    · cases o
      · exact Or.inr rfl
      · exact Or.inl rfl

lemma rev_ne (l : Dart n w) : rev n w l ≠ l := by
  intro h
  have hh := congrArg Prod.snd h
  cases hc : l.2 <;> simp [rev,hc] at hh

/-- Reversed label sides at the SAME indexed position are literally opposite
indexed steps. This excludes indexed loops in the coincidence-contact graph. -/
lemma raw_position_reverse {s t : WalkStep n w d}
    (hs : isLetter n w (walkLabel n w d s) = true)
    (ht : isLetter n w (walkLabel n w d t) = true)
    (hp : rawPosition n w d s = rawPosition n w d t)
    (he : walkLabel n w d t = rev n w (walkLabel n w d s)) :
    t = walkOpposite n w d s := by
  have hc := raw_step_cases n w d s hs
  have hd := raw_step_cases n w d t ht
  rw [← hp] at hd
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · rw [hc,hd] at he
    exact False.elim (rev_ne n w _ he.symm)
  · rw [hc,hd]
  · rw [hc,hd,walkOpposite_twice]
  · rw [hc,hd] at he
    exact False.elim (rev_ne n w _ he.symm)

universe u
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma contact_different (hred : P.FullyReduced) (x : P.Dart)
    (hx : isLetter n w (walkLabel n w d (P.index x)) = true) :
    rawPosition n w d (P.index x) ≠ rawPosition n w d (P.index (P.pairing.edge x)) := by
  intro hp
  have he : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  apply hred x
  apply raw_position_reverse n w d hx _ hp he
  rw [he]
  exact hx

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
