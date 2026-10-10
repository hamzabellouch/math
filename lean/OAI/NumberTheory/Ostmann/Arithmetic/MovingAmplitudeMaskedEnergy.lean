import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeHarmonicCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedTemplateEnergy

namespace OAI

/-! # The actual one-branch amplitude energy in restored arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators

private theorem amplitude_energy_fubini {U T X Y S : Type}
    [Fintype U] [Fintype X] [Fintype Y] [Fintype S]
    (I : Finset T) (M : U → ℝ) (w : T → ℝ) (ρ : X → ℝ) (ν : Y → ℝ)
    (F : U → T → X → Y → S → ℝ) :
    (∑ u, M u * ∑ p ∈ I, w p * ∑ a : X × (Y × S),
      (ρ a.1 * ν a.2.1) * F u p a.1 a.2.1 a.2.2) =
    ∑ u, M u * ∑ y, ν y * ∑ p ∈ I, w p * ∑ x, ρ x * ∑ s, F u p x y s := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The compensation draw and the surviving draw are independent original
priors; this reordering introduces no frequency probability factor. -/
theorem movingAmplitudeRegularEnergy_fubini
    (P Pg I : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg =
    ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
      ∑ y : MovingRegularSlot n r m → P, (∏ i, primeSubsetPrior P (Q i) (y i)) *
        ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
          ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
            ∑ s : transferFrequencyRange (V n),
              ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
                n (4 + r) m s.val (movingRestoreSample n r m u y) p X *
                primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (X : ℕ))
                  (∏ i, (y i : ℕ)) s.val‖ ^ 2 := by
  unfold movingAmplitudeRegularEnergy
  dsimp only
  have h := amplitude_energy_fubini
    (U := TreeLeafIndex n × Fin 4 → P) (X := Pg)
    (Y := MovingRegularSlot n r m → P) (S := transferFrequencyRange (V n)) I
    (fun u => (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ))
    (fun p => φ (Real.log p - G (n + 1)))
    (smoothGiantPrior Pg φ (G (n + 1)))
    (fun y => ∏ i, primeSubsetPrior P (Q i) (y i))
    (fun u p X y s =>
      ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p X *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (X : ℕ))
          (∏ i, (y i : ℕ)) s.val‖ ^ 2)
  convert h using 1
  simp only [movingAmplitudePrior, Nat.cast_prod]

/-- This is the literal arithmetic energy under the original restored prior.
The extracted compensation product is a weight, not a change of measure. -/
theorem movingAmplitudeRegularEnergy_eq_masked
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg =
      movingMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg
        (fun x => (movingRestoredCompensationProduct Subtype.val n r m x : ℝ)) := by
  rw [movingAmplitudeRegularEnergy_fubini]
  unfold movingMaskedTemplateEnergy
  rw [movingTemplateRestoredPrior_average_real]
  simp only [movingRestoredCompensationProduct_restore, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro s _
  rw [movingMaskedTemplateKernel_restore]
  ring

/-- The compensation cost is now explicit, with the same original prior in
both energies. The bound is used only after the nonnegative diagonal reduction. -/
theorem movingAmplitudeRegularEnergy_le_masked
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (b : ℝ) (hb : ∀ a, μ n a ≠ 0 → (a : ℝ) ≤ Real.exp b) :
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg ≤
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b) *
        movingMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg
          (fun _ => 1) := by
  rw [movingAmplitudeRegularEnergy_eq_masked P Pg I hP]
  apply movingMaskedTemplateEnergy_weight_le P Pg I hP outside μ hμ
    childBound pivotBound V F φ hφ G n r m Q greg
  intro x hx
  exact movingRestoredCompensationProduct_le_exp P (μ n) n r m
    (fun i => primeSubsetPrior P (Q i)) b hb x hx

end Ostmann

end OAI
