import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellTarget

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch PictureSwitch.PolygonTarget
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def leftDart (f : FanTriangle n w) : Dart n w := (.inr ⟨f.1,fanLeft n w f⟩,true)
def rightDart (f : FanTriangle n w) : Dart n w := (.inr ⟨f.1,fanRight n w f⟩,true)

def dartPart (l : Dart n w) : Bool :=
  match l.1 with
  | .inl _ => false
  | .inr v => linePart v.2.val

lemma left_part (f : FanTriangle n w) : dartPart n w (leftDart n w f) = false := rfl
lemma right_part (f : FanTriangle n w) : dartPart n w (rightDart n w f) = true := rfl

lemma endpoints_injective {f g : FanTriangle n w}
    (hl : leftDart n w f = leftDart n w g) (hr : rightDart n w f = rightDart n w g) : f = g := by
  rcases f with ⟨b,e⟩; rcases g with ⟨c,k⟩
  have hb : b = c := Sum.inr.inj (congrArg (start n w) hl)
  subst c
  have hleft : fanLeft n w ⟨b,e⟩ = fanLeft n w ⟨b,k⟩ :=
    (radialLabel_bijective n w b).1 (Subtype.ext hl)
  have hright : fanRight n w ⟨b,e⟩ = fanRight n w ⟨b,k⟩ :=
    (radialLabel_bijective n w b).1 (Subtype.ext hr)
  have he : e = k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Sum.inl.inj (congrArg Subtype.val hleft)
    · exact Sum.inr.inj (congrArg Subtype.val hright)
  cases he
  rfl

def corner (f : FanTriangle n w) (o : Bool) : (boundary n w d).Side :=
  ⟨.inl f,o,if o then (0 : Fin 3) else (2 : Fin 3)⟩

def cornerOut (f : FanTriangle n w) (o : Bool) : Dart n w :=
  if o then leftDart n w f else rightDart n w f

def cornerIn (f : FanTriangle n w) (o : Bool) : Dart n w :=
  if o then rightDart n w f else leftDart n w f

lemma corner_label (f : FanTriangle n w) (o : Bool) :
    (boundary n w d).sideLabel (corner n w d f o) = cornerOut n w f o := by
  cases o <;> rfl

lemma corner_previous_label (f : FanTriangle n w) (o : Bool) :
    rev n w ((boundary n w d).sideLabel ((boundary n w d).next⁻¹ (corner n w d f o))) =
      cornerIn n w f o := by
  cases o <;> rfl

lemma corner_start (f : FanTriangle n w) (o : Bool) :
    start n w ((boundary n w d).sideLabel (corner n w d f o)) = .inr f.1 := by
  cases o <;> rfl

/-- These are precisely the two orientations of the apex corner of an
actual indexed fan triangle. No quotient by generator labels is made. -/
lemma apex_side_corner (f : FanTriangle n w) (o : Bool) (i : Fin 3)
    (ha : isApex n w (start n w ((boundary n w d).sideLabel ⟨.inl f,o,i⟩)) = true) :
    (⟨.inl f,o,i⟩ : (boundary n w d).Side) = corner n w d f o := by
  cases o <;> fin_cases i
  · cases ha
  · simp [Boundary.sideLabel,boundary,side,fanSide,rev_letter,start_letter,isApex] at ha
  · rfl
  · rfl
  · simp [Boundary.sideLabel,boundary,side,fanSide,start_letter,isApex] at ha
  · cases ha

lemma corner_bipartite (f : FanTriangle n w) (o : Bool) :
    dartPart n w (cornerOut n w f o) ≠ dartPart n w (cornerIn n w f o) := by
  cases o
  · change true ≠ false
    decide
  · change false ≠ true
    decide

/-- A reversed pair of apex corner ports determines the SAME fan triangle
with opposite orientation. This is the actual simple bipartite fan graph
fact that rules out a triangle-only two-step link in a reduced picture. -/
lemma reverse_corner_unique {f g : FanTriangle n w} {o p : Bool}
    (hout : cornerOut n w f o = cornerIn n w g p)
    (hin : cornerIn n w f o = cornerOut n w g p) : g = f ∧ p = !o := by
  cases o <;> cases p
  · have he := congrArg (dartPart n w) hout
    cases he
  · exact ⟨(endpoints_injective n w hin hout).symm,rfl⟩
  · exact ⟨(endpoints_injective n w hout hin).symm,rfl⟩
  · have he := congrArg (dartPart n w) hout
    cases he

lemma reverse_corner_index (f : FanTriangle n w) (o : Bool) :
    (boundary n w d).next⁻¹ (corner n w d f (!o)) =
      (boundary n w d).opposite (corner n w d f o) := by
  cases o <;> rfl

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
