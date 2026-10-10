import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellTarget

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

include hc in
lemma stepLetter_value {a b : MasterGraph.Vertex} (s : MasterGraph.Step a b)
    (l : Field → Alphabet n) :
    c (letterDart n w (stepLetter n l s)) = s.value l (c ∘ letterDart n w) := by
  have hr : ∀ a, c (letterDart n w (inverseLetter n a)) = (c (letterDart n w a))⁻¹ :=
    fun a => hc (letterDart n w a)
  cases h : s.forward <;> simp only [stepLetter,MasterGraph.Step.value,h,
    Bool.false_eq_true,ite_false,ite_true,hr,Function.comp_apply]

include hc hcell in
lemma square_relator_value (l : Field → Alphabet n) (τ : TwoPath)
    (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
    MasterGraph.squareWord l (c ∘ letterDart n w) τ = 1 := by
  let s : Square n w := ⟨τ,⟨fun f => l f.val,present⟩⟩
  let l' := extendRow n (.inr (.inr τ)) s.2.val
  have hf := hcell (.inr (.inr (.inl s)))
  change c (letterDart n w (stepLetter n l' (MasterGraph.first τ))) *
    (c (letterDart n w (stepLetter n l' (MasterGraph.second τ))) *
      (c (letterDart n w (l' (.inr (τ,0)))) *
        (c (letterDart n w (l' (.inr (τ,1)))) * 1))) = 1 at hf
  rw [stepLetter_value n w c hc,stepLetter_value n w c hc,mul_one] at hf
  have hl : ∀ f ∈ squareSupport τ, l' f = l f := by
    intro f hf
    simp only [l',extendRow,show f ∈ rowSupport (.inr (.inr τ)) from hf,dite_eq_left,s]
  have h1 := hl (MasterGraph.first τ).field (by simp [MasterGraph.first_field,squareSupport])
  have h2 := hl (MasterGraph.second τ).field (by simp [MasterGraph.second_field,squareSupport])
  have h3 := hl (.inr (τ,0)) (by simp [squareSupport])
  have h4 := hl (.inr (τ,1)) (by simp [squareSupport])
  simp only [MasterGraph.Step.value,Function.comp_apply,h1,h2,h3,h4] at hf
  simpa only [MasterGraph.squareWord,MasterGraph.Step.value,Function.comp_apply,mul_assoc] using hf

include hcell in
lemma six_relator_value (x : Fin 6 → Alphabet n) (present : d x = true) :
    (List.ofFn ((c ∘ letterDart n w) ∘ x)).prod = 1 := by
  exact hcell (.inr (.inr (.inr ⟨x,present⟩)))

end HyperbolicObstruction.ConeSkeleton
end

end OAI
