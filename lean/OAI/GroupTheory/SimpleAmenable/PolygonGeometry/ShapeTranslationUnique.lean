import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ShapeTranslationUnique
open Classical Set

theorem real_sSup_translate {A : Set ℝ} (hne : A.Nonempty) (hb : BddAbove A) (u : ℝ) :
    sSup ((fun x => x+u) '' A)=sSup A+u := by
  have hi : ((fun x => x+u) '' A).Nonempty := hne.image _
  have hbi : BddAbove ((fun x => x+u) '' A) := by
    obtain ⟨M,hM⟩ := hb
    exact ⟨M+u,by rintro y ⟨x,hx,rfl⟩; dsimp; linarith [hM hx]⟩
  apply le_antisymm
  · apply csSup_le hi
    rintro y ⟨x,hx,rfl⟩
    dsimp; linarith [le_csSup hb hx]
  · have h : sSup A ≤ sSup ((fun x => x+u) '' A)-u := by
      apply csSup_le hne
      intro x hx
      have hh := le_csSup hbi (show x+u∈(fun x => x+u) '' A from ⟨x,hx,rfl⟩)
      linarith
    linarith

theorem bounded_coordinate_shift_unique {X Y : Type*} (A : Set X) (φ : X → ℝ) (ψ : Y → ℝ)
    (hne : A.Nonempty) (hb : BddAbove (φ '' A)) (f h : X → Y)
    (he : f '' A=h '' A) (u v : ℝ)
    (hu : ∀x∈A,ψ (f x)=φ x+u) (hv : ∀x∈A,ψ (h x)=φ x+v) : u=v := by
  have him (f : X → Y) (u : ℝ) (hf : ∀x∈A,ψ (f x)=φ x+u) :
      ψ '' (f '' A)=(fun x => x+u) '' (φ '' A) := by
    rw [Set.image_image,Set.image_image]
    apply Set.image_congr
    intro x hx
    exact hf x hx
  have hx := congrArg (fun T : Set Y => sSup (ψ '' T)) he
  rw [him f u hu,him h v hv,real_sSup_translate (hne.image φ) hb,
    real_sSup_translate (hne.image φ) hb] at hx
  linarith

end ShapeTranslationUnique

end SimpleAmenable
end
end

end OAI
