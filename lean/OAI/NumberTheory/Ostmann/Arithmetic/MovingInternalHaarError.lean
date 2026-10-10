import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalAverageError

namespace OAI

/-! # Averaging the relative square loss under the original mixed Haar law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_haar_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    ‖(Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2)‖ ≤
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
        ∑ z : ZMod p × (ZMod p)ˣ, ‖movingInternalBaseFactor value T p z.1 z.2‖ := by
  rw [externalSquare_raw_average p (movingInternalPairFactor value T p), norm_mul,
    norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ =>
    movingInternalPairFactor_normalized_fiber_norm_le value T p z.1 z.2)

theorem movingInternalPairFactor_haar_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0)) :
    ‖(Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2) -
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod p × (ZMod p)ˣ, movingInternalBaseFactor value T p z.1 z.2)‖ ≤
      (2 * (2 ^ n - 1 : ℕ) / (p : ℝ)) *
        ((Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
          ∑ z : ZMod p × (ZMod p)ˣ, ‖movingInternalBaseFactor value T p z.1 z.2‖) := by
  let c : ℂ := (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹
  let w : ℝ := (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹
  let K : ℝ := 2 * (2 ^ n - 1 : ℕ) / (p : ℝ)
  let H := fun z : ZMod p × (ZMod p)ˣ => ((p : ℂ) ^ 2)⁻¹ *
    ∑ v : SquareLiftPairs p z.1 (z.2 : ZMod p), movingInternalPairFactor value T p v.1.1 v.2.1
  let G := fun z : ZMod p × (ZMod p)ˣ => movingInternalBaseFactor value T p z.1 z.2
  have havg : (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2) =
      c * ∑ z, H z := by
    exact externalSquare_raw_average p (movingInternalPairFactor value T p)
  have he (z : ZMod p × (ZMod p)ˣ) : ‖H z - G z‖ ≤ K * ‖G z‖ :=
    movingInternalPairFactor_normalized_fiber_error tier value hprime hdisjoint T hlevels p hf
      z.1 z.2 (Units.ne_zero z.2)
  have hc : ‖c‖ = w := by simp only [c, w, norm_inv, Complex.norm_natCast]
  have hw : 0 ≤ w := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [havg]
  change ‖c * (∑ z, H z) - c * (∑ z, G z)‖ ≤ K * (w * ∑ z, ‖G z‖)
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, hc]
  calc
    w * ‖∑ z, (H z - G z)‖ ≤ w * ∑ z, ‖H z - G z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ ≤ w * ∑ z, K * ‖G z‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => he z) hw
    _ = _ := by rw [← Finset.mul_sum]; ring

end Ostmann

end OAI
