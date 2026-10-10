import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitudeRestore
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateWeightedSupport

namespace OAI

/-! # The surviving giant, regular tuple and frequency as one transfer index -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingAmplitudeIndex (σ : Type) (Pg : Finset ℕ) (n r m : ℕ) (V : ℕ → ℕ) :=
  Pg × ((MovingRegularSlot n r m → σ) × transferFrequencyRange (V n))

noncomputable def movingAmplitudePrior {σ : Type} (Pg : Finset ℕ) (n r m : ℕ)
    (V : ℕ → ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (a : MovingAmplitudeIndex σ Pg n r m V) : ℝ :=
  ρ a.1 * ∏ i, ν i (a.2.1 i)

/-- The frequency is part of the transfer index and has counting measure.
Only the giant and regular prime coordinates carry probability weights. -/
theorem movingTemplatePrimeAmplitude_index {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
      Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable =
    ∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
      ∑ p : Pg, (ρ p : ℂ) * ∑ a : MovingAmplitudeIndex σ Pg n r m V,
        movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m
          (fun a => a.2.2.val) (fun a => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ))
          (fun a => (a.1 : ℕ)) (fun a => a.2.1) u p a *
          movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then (p : ℕ) else (a.1 : ℕ))
              (value ∘ movingRestoreSample n r m u a.2.1))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod a.2.2.val := by
  rw [movingTemplatePrimeAmplitude_restore]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  simp only [MovingAmplitudeIndex, Fintype.sum_prod_type, movingTemplateTransferWeight,
    movingAmplitudePrior, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  ring

end Ostmann

end OAI
