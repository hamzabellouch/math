import Mathlib
import OAI.Geometry.HyperbolicGroups.CoreFan
import OAI.Geometry.HyperbolicGroups.Presentation
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.MappedPicture

namespace OAI

section
section


noncomputable section
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation

variable (n : ℕ)
abbrev FanRow := Σ i : Fin 7, rowSupport (.inl i) → Alphabet n
variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

/-- Fan occurrences are the actual included rows, counted once even if several
top occurrences use them. Positions are NOT identified by generator labels. -/
abbrev Fan := {b : FanRow n // w ⟨.inl b.1,b.2⟩ = true}

abbrev Vertex := Unit ⊕ Fan n w
abbrev Edge := Fin (n+1) ⊕ (Σ b : Fan n w, FanVertex b.val.1)
abbrev Dart := Edge n w × Bool

def start : Dart n w → Vertex n w
  | (.inl _,_) => .inl ()
  | (.inr b,true) => .inr b.1
  | (.inr _,false) => .inl ()

def rev (l : Dart n w) : Dart n w := (l.1,!l.2)
def isApex : Vertex n w → Bool
  | .inl _ => false
  | .inr _ => true

lemma radial (l : Dart n w) (h : isApex n w (start n w l) = true) :
    isApex n w (start n w (rev n w l)) = false := by
  rcases l with ⟨e,b⟩; cases e <;> cases b <;> simp_all [start,isApex,rev]

abbrev Outgoing (f : Fan n w) := {l : Dart n w // start n w l = .inr f}

def radialLabel (f : Fan n w) (v : FanVertex f.val.1) : Outgoing n w f :=
  ⟨(.inr ⟨f,v⟩,true),rfl⟩

lemma radialLabel_bijective (f : Fan n w) : Function.Bijective (radialLabel n w f) := by
  constructor
  · intro a b h
    have hs : (⟨f,a⟩ : Σ b : Fan n w, FanVertex b.val.1) = ⟨f,b⟩ :=
      Sum.inr.inj (congrArg (fun d => d.val.1) h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  · rintro ⟨⟨e,b⟩,h⟩
    rcases e with e | ⟨f',v⟩
    · simp [start] at h
    · cases b with
      | false => simp [start] at h
      | true =>
        have he : f' = f := Sum.inr.inj h
        subst f'
        exact ⟨v,rfl⟩

instance (f : Fan n w) : Fintype (Outgoing n w f) :=
  Fintype.ofEquiv (FanVertex f.val.1) (Equiv.ofBijective _ (radialLabel_bijective n w f))

lemma card_outgoing (f : Fan n w) : Fintype.card (Outgoing n w f) ≤ 5 := by
  classical
  rw [← Fintype.card_congr (Equiv.ofBijective _ (radialLabel_bijective n w f))]
  exact card_fanVertex_le f.val.1

/-- The source's reduced target one-skeleton, after top cone neighborhoods
have been assembled into macro polygons. Every created apex-link now has at
most five steps. The genus-zero side pairing is PRODUCED, not a hypothesis
about some already-normalized picture. Its face permutation is unchanged. -/
theorem normalize {D : Type*} [DecidableEq D] [Fintype D]
    (M : PictureSwitch.PictureMap D) (label : D → Dart n w)
    (hM : M.Respects label (start n w) (rev n w)) (hG : M.GenusZero) :
    ∃ N : PictureSwitch.PictureMap D,
      N.face = M.face ∧ N.Respects label (start n w) (rev n w) ∧ N.GenusZero ∧
      (∀ a b, isApex n w (start n w (label a)) = true →
        N.vertex.SameCycle a b → label a = label b → a = b) ∧
      ∀ a f, start n w (label a) = .inr f →
        Fintype.card {x : D // N.vertex.SameCycle a x} ≤ 5 := by
  classical
  obtain ⟨N,hface,hN,hzero,hinj⟩ := PictureSwitch.PictureMap.normalize_radial
    (isApex n w) hM hG (fun d => radial n w (label d))
  refine ⟨N,hface,hN,hzero,hinj,?_⟩
  intro a f ha
  have hconstant : ∀ {x y : D}, N.vertex.SameCycle x y →
      start n w (label x) = start n w (label y) :=
    fun {x y} h => (PictureSwitch.sameCycle_le_of_apply
      (s := Setoid.ker (start n w ∘ label)) (fun x => (hN.1 x).symm)) h
  let g : {x : D // N.vertex.SameCycle a x} → Outgoing n w f := fun x =>
    ⟨label x.val,(hconstant x.property).symm.trans ha⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.val y.val
    · rw [← hconstant x.property,ha]; rfl
    · exact x.property.symm.trans y.property
    · exact congrArg Subtype.val hxy
  exact (Fintype.card_le_of_injective g hg).trans (card_outgoing n w f)

end ConeSkeleton
end HyperbolicObstruction
end
end

section

end
end

end OAI
