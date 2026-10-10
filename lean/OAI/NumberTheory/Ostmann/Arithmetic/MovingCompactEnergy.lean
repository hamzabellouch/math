import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompactLeaf
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateExternalMultiplier
import OAI.NumberTheory.Ostmann.Characters.MixedExternalAverage

namespace OAI

/-! # Frequency truncation preserves the actual unsymmetrized energy -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem mixedExternalAverage_frequency_congr {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ s, s.natAbs ≤ N → ∀ y x z, F s y x z = H s y x z) :
    mixedExternalAverage ν N u v r w center F =
      mixedExternalAverage ν N u v r w center H := by
  rw [mixedExternalAverage_finite, mixedExternalAverage_finite]
  apply Finset.sum_congr rfl
  intro x _
  rw [h x.1.val ((mem_transferFrequencyRange _ _).mp x.1.property)]

theorem movingTemplate_compact_energy {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (law : MovingRegularSlot n r m → σ → ℝ)
    (W : ℤ → (MovingRegularSlot n r m → σ) → ℝ → ℝ → ℂ)
    (u v a b center : ℝ) :
    mixedExternalAverage law (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1)
          g Dq S ψ X lo hi) φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) * W s y x z) =
    mixedExternalAverage law (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => movingCompactLeaf (V 0))
          g Dq S ψ X lo hi) φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) * W s y x z) := by
  apply mixedExternalAverage_frequency_congr
  intro s hs y x z
  rw [movingTemplateCoefficient_original_leaf_congr value q outside μ childBound pivotBound V
    (fun s => if s = 0 then 0 else 1) (movingCompactLeaf (V 0))
    (fun s hs => by simp only [movingCompactLeaf, hs, ite_true])
    g Dq S ψ X lo hi φ G n r m s hs]

end Ostmann

end OAI
