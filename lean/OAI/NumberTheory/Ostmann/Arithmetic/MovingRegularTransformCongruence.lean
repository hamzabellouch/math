import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeTerms
import OAI.NumberTheory.Ostmann.Construction.PrimeMaskExtension

namespace OAI

/-! # Changing regular tests away from the sampled alphabet changes no statistic -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingTaggedTransform_regular_congr {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (greg hreg ggiant : ∀ r : ℕ, ZMod r → ℂ)
    (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) (hregEq : ∀ j, greg (q j) = hreg (q j)) :
    movingTaggedTransform (Sum.elim p q) (Sum.elim (fun _ => true) (fun _ => false))
      greg ggiant favorable D s =
    movingTaggedTransform (Sum.elim p q) (Sum.elim (fun _ => true) (fun _ => false))
      hreg ggiant favorable D s := by
  unfold movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i with
  | inl i => rfl
  | inr j => simp only [Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, hregEq j]

theorem movingTemplatePrimeAmplitude_regular_congr {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg hreg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hregEq : ∀ a, greg (value a) = hreg (value a)) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      Pg ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      Pg ρ ν hreg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  have ht (p : Bool → ℕ) (y : MovingRegularSlot n r m → σ) (D : ℕ) (s : ℤ) :
      movingTaggedTransform (Sum.elim p (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
      movingTaggedTransform (Sum.elim p (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) hreg ggiant favorable D s :=
    movingTaggedTransform_regular_congr p (value ∘ y) greg hreg ggiant favorable D s
      (fun i => hregEq _)
  simp_rw [ht]

theorem movingAmplitudeDiagonal_regular_congr {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg I : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg hreg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hregEq : ∀ a, greg (value a) = hreg (value a)) :
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m
      Pg I ρ ν greg ggiant favorable =
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m
      Pg I ρ ν hreg ggiant favorable := by
  unfold movingAmplitudeDiagonal
  dsimp only
  simp_rw [show ∀ X (y : MovingRegularSlot n r m → σ) D s,
    movingTaggedTransform (movingOneGiantModuli X (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingTaggedTransform (movingOneGiantModuli X (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) hreg ggiant favorable D s from
    fun X y D s => movingTaggedTransform_regular_congr (fun _ : Unit => X)
      (value ∘ y) greg hreg ggiant favorable D s (fun i => hregEq _)]

end Ostmann

end OAI
