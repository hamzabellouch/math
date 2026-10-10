import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedTemplateEnergy
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantMixedInterval

namespace OAI

/-! # The masked energy with its exact integer and harmonic-prime scales -/

namespace Ostmann
open scoped Classical BigOperators

private theorem masked_energy_fubini {S A X T : Type}
    [Fintype S] [Fintype A] [Fintype X]
    (I : Finset T) (M : A → ℂ) (w : T → ℂ) (ρ : X → ℂ)
    (F : S → A → T → X → ℂ) :
    (∑ a, M a * ∑ p ∈ I, w p * ∑ x, ρ x * ∑ s, F s a p x) =
    ∑ s, ∑ a, M a * ∑ x, ρ x * ∑ p ∈ I, w p * F s a p x := by
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext p
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem movingMaskedTemplateEnergy_interval
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center : ℝ) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let I := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    (movingMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg
      (fun _ => 1) : ℂ) =
    (Real.exp (smoothGiantLogNormalizer Pg φ H + center) : ℂ) *
      mixedExternalAverage ν (V n) (H - 1) (H + 1) (H - 1) (H + 1) center
        (fun s x z y => (φ (z - H) : ℂ) * (φ (y - H) : ℂ) *
          (movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg
            x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s : ℝ)) := by
  intro H Pg I ν
  have h := smoothGiant_mixed_external_interval ν (V n) φ H H center hout
    (fun s x p q => (movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G
      n r m greg x p q s : ℝ))
  apply Eq.trans _ h
  unfold movingMaskedTemplateEnergy
  simp only [one_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  have hf := masked_energy_fubini (S := transferFrequencyRange (V n))
    (A := MovingRegularSlot n (4 + r) m → P) (X := Pg) (T := ℕ) I
    (fun x => ((∏ i, ν i (x i) : ℝ) : ℂ))
    (fun p => (φ (Real.log p - H) : ℂ))
    (fun q : Pg => (smoothGiantPrior Pg φ H q : ℂ))
    (fun s x p q => (movingMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G
      n r m greg x p q s.val : ℝ))
  convert hf using 1
  simp only [Pg, I, finite_univ_canonical]

end Ostmann

end OAI
