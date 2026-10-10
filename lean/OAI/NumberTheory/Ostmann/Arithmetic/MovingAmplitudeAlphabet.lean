import OAI.NumberTheory.Ostmann.Arithmetic.MovingAlphabetRestriction
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

/-! # The literal prime amplitude is unchanged by restricting live regular primes -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplatePrimeAmplitude_original_alphabet {A B I : Type}
    [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → A → ℝ)
    (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e)
    (hν : ∀ i a, ν i a ≠ 0 → a ∈ Set.range e)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q (fun T => F (T.map e)) g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i b => ν i (e b)) greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have he := productPrior_alphabet_sum e ν (fun y =>
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m s.val y XL XR *
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val) hν
  simp only [finite_univ_canonical] at he ⊢
  rw [he]
  apply Finset.sum_congr rfl
  intro y _
  rw [movingTemplateCoefficient_original_alphabet e q value outside μ childBound pivotBound V
    F g Dq S ψ X lo hi φ G n r m s.val y XL XR hμ]
  rfl

end Ostmann

end OAI
