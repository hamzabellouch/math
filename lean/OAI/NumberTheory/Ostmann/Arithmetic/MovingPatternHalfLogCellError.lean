import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternHalfLogKernelCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCost
import OAI.NumberTheory.Ostmann.Arithmetic.BulkWeightedErrorRate

namespace OAI

/-! # Cell error with terminal log cutoffs retained -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

/-- The cell threshold is uniform over the moving Fourier window. -/
theorem PublishedProgressionInput.movingPattern_half_log_cell_error_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D F Cnorm Dlog : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hDlog : 0 ≤ Dlog) (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ n) :
    ∃ C : ℝ, 1 ≤ C ∧ Cnorm ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      ∀ (Cell : Type) [Fintype Cell] (M Q : ℕ) [NeZero M], 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      ∀ (p : Fin m → ℕ) (Z : (TreeLeafIndex n × Fin m) → ℝ)
        (a : ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) → ℂ) (amp T : ℝ) (rlog : ℕ),
      rlog ≤ 2 ^ n * (r₀ + m + 4 * n) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp (C * L)) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) →
      0 ≤ amp → amp ≤ Real.exp (F * m) →
      (∀ z, ‖a z‖ ≤ amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      ∀ u : (TreeLeafIndex n × Fin m) → Cell → ℝ, (∀ j c, T ≤ u j c) →
      (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell,
        ∑ z : (TreeLeafIndex n × Fin m) → (ZMod M)ˣ, ‖a z‖ *
          (2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
            bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
              (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog B D Dlog *
              bulkPrimeErrorFactor P Q (u j (c j))) ≤
        Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  obtain ⟨C₀, hC₀, hkernel⟩ := movingPatternHalfLogKernelBudget_spectatorScale_window ψ n r₀ k A H B D Dlog hA hH hDlog
  let K := (F + 1) * ((k : ℝ) ^ 4 + 1)
  let C := max C₀ ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K)
    -- The dimension is also charged in the same constant.
  let C' := max (max C (((2 ^ n : ℕ) : ℝ) * (k : ℝ) ^ 4)) Cnorm
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC₀C : C₀ ≤ C' := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hC' : 1 ≤ C' := hC₀.trans hC₀C
  refine ⟨C', hC', le_max_right _ _, ?_⟩
  filter_upwards [P.bulk_weighted_error_rate C' hC', eventually_ge_atTop (1 : ℝ)] with L hrate hL
  dsimp only
  intro lo hi hhi hwidth Cell _ M Q _ hQ hQlog p Z a amp T rlog hrlog hp hZ0 hZ hcell hunit hamp0 hamp ha hT u hu
  let m := spectatorBulkCount k L
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hFK : F * (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hKk : (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hF (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)]
  have hmK : (m : ℝ) ≤ K * L := hm.trans (mul_le_mul_of_nonneg_right hKk hL0)
  have hampK : amp ≤ Real.exp (K * L) := hamp.trans (Real.exp_le_exp.mpr (by
    exact (mul_le_mul_of_nonneg_left hm hF).trans (by nlinarith [mul_le_mul_of_nonneg_right hFK hL0])))
  let bound := amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))
  have hbound0 : 0 ≤ bound := mul_nonneg hamp0 (Finset.prod_nonneg fun i _ => by positivity)
  have hbound : bound ≤ Real.exp (C' * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (moving_spectator_linear_cost n m p K L amp hK hL0 hamp0 hmK hampK hp).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hL0
    exact (le_max_right C₀ _).trans ((le_max_left C _).trans (le_max_left _ _))
  have hdim : (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ≤ C' * L := by
    simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ (2 ^ n : ℕ) * ((k : ℝ) ^ 4 * L) :=
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
      _ ≤ C' * L := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hL0
  have hbudget := hkernel L hL lo hi hhi hwidth tlog rlog htlog hrlog
  have hbudget' : bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog B D Dlog ≤
      Real.exp (C' * L ^ 2) :=
    hbudget.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC₀C (sq_nonneg L)))
  have hb := @hrate (TreeLeafIndex n × Fin m) Cell inferInstance inferInstance M Q
    inferInstance hQ hQlog Z a bound
    (bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog B D Dlog)
    T hZ0 hbound0 (by
      have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
      unfold bulkLogWeightedKernelPairBudget
      positivity)
    hdim hZ hcell hunit hbound hbudget' ha hT u hu
  simpa only [finite_univ_canonical] using hb

end Ostmann

end OAI
