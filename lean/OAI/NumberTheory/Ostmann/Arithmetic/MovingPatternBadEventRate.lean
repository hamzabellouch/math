import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelGain
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCost
import OAI.NumberTheory.Ostmann.Arithmetic.BulkDeletionRate

namespace OAI

/-! # Collision and deletion errors for the actual pattern kernel -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem movingPattern_bad_event_rate (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A lo hi B D F Cnorm : ℝ) (hA : 0 ≤ A) (hhi : lo ≤ hi) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (S deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (Z : (TreeLeafIndex n × Fin m) → ℝ) (amp H T : ℝ),
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp H) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cnorm * L)) → H ≤ Cnorm * L →
      0 ≤ amp → amp ≤ Real.exp (F * m) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ)) →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      let cost := amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
      cost * (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
        cost * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale ψ n r₀ k
    A lo hi B D hA hhi
  let K := (F + 1) * ((k : ℝ) ^ 4 + 1)
  let C := max (max Cnorm Cw)
    (max ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K) (((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4))
  have hCwC : Cw ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC : 1 ≤ C := hCw.trans hCwC
  have hCn : Cnorm ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCs : (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCd : ((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [bulk_collision_deletion_rate C hC, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  dsimp only
  intro p S deleted Z amp H T hp hZ0 hZ hdel hH hamp0 hamp hT hlow
  let m := spectatorBulkCount k L
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  let cost := amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
  have hL0 : 0 ≤ L := by linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFk : F * (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hkK : (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hF (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)]
  have hm := spectatorBulkCount_upper k L hL0
  have hmK : (m : ℝ) ≤ K * L := hm.trans (mul_le_mul_of_nonneg_right hkK hL0)
  have hampK : amp ≤ Real.exp (K * L) := hamp.trans (Real.exp_le_exp.mpr (by
    exact (mul_le_mul_of_nonneg_left hm hF).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hFk hL0])))
  have hspec := moving_spectator_linear_cost n m p K L amp hK hL0 hamp0 hmK hampK hp
  have hspec' : amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hL0) (Real.exp_nonneg _)
  have hW : W ≤ Real.exp (C * L ^ 2) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    exact (hkernel L hL).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))
  have hcost0 : 0 ≤ cost := by dsimp only [cost, W]; positivity
  have hcost : cost ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul hspec' hW (sq_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, add_comm]
  have hdim : (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ≤ C * L := by
    simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCd hL0)
  have hCnL := mul_le_mul_of_nonneg_right hCn hL0
  exact hrate (TreeLeafIndex n × Fin m) S deleted Z H T (Real.exp (Cnorm * L)) cost
    hZ0 hZ hdel (Real.exp_nonneg _) hcost0 hdim
    (Real.exp_le_exp.mpr hCnL) (hH.trans hCnL) hcost hT hlow

/-- Collision and deletion errors uniformly over the moving Fourier window. -/
theorem movingPattern_bad_event_rate_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D F Cnorm : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      ∀ (p : Fin m → ℕ) (S deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (Z : (TreeLeafIndex n × Fin m) → ℝ) (amp H T : ℝ),
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp H) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cnorm * L)) → H ≤ Cnorm * L →
      0 ≤ amp → amp ≤ Real.exp (F * m) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ)) →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      let cost := amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
      cost * (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
        cost * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale_window ψ n r₀ k
    A H B D hA hH
  let K := (F + 1) * ((k : ℝ) ^ 4 + 1)
  let C := max (max Cnorm Cw)
    (max ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K) (((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4))
  have hCwC : Cw ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC : 1 ≤ C := hCw.trans hCwC
  have hCn : Cnorm ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCs : (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCd : ((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [bulk_collision_deletion_rate C hC, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  dsimp only
  intro lo hi hhi hwidth p S deleted Z amp H T hp hZ0 hZ hdel hH hamp0 hamp hT hlow
  let m := spectatorBulkCount k L
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  let cost := amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
  have hL0 : 0 ≤ L := by linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFk : F * (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hkK : (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hF (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)]
  have hm := spectatorBulkCount_upper k L hL0
  have hmK : (m : ℝ) ≤ K * L := hm.trans (mul_le_mul_of_nonneg_right hkK hL0)
  have hampK : amp ≤ Real.exp (K * L) := hamp.trans (Real.exp_le_exp.mpr (by
    exact (mul_le_mul_of_nonneg_left hm hF).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hFk hL0])))
  have hspec := moving_spectator_linear_cost n m p K L amp hK hL0 hamp0 hmK hampK hp
  have hspec' : amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hL0) (Real.exp_nonneg _)
  have hW : W ≤ Real.exp (C * L ^ 2) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    exact (hkernel L hL lo hi hhi hwidth).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))
  have hcost0 : 0 ≤ cost := by dsimp only [cost, W]; positivity
  have hcost : cost ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul hspec' hW (sq_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, add_comm]
  have hdim : (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ≤ C * L := by
    simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCd hL0)
  have hCnL := mul_le_mul_of_nonneg_right hCn hL0
  exact hrate (TreeLeafIndex n × Fin m) S deleted Z H T (Real.exp (Cnorm * L)) cost
    hZ0 hZ hdel (Real.exp_nonneg _) hcost0 hdim
    (Real.exp_le_exp.mpr hCnL) (hH.trans hCnL) hcost hT hlow

end Ostmann

end OAI
