import OAI.Combinatorics.EditApproximation.Coarse.CoarseWidthWork
import OAI.Combinatorics.EditApproximation.Geometry.DependencyPathEnvelope

namespace OAI

/-! The actual coarse array counter has a common source-width overhead.
Its exponent is sublinear in the computed logarithmic height. -/

namespace EditApproximation

open MeasureTheory

def computedCoarseWidthOverhead (N : ℕ) : ℕ :=
  6 * (integerParameters N).B * (Nat.clog 2 N + 1) * (computedMaxCoarseDepth N + 1) *
    inputHeight N ^ (8 * computedMaxCoarseDepth N)

theorem coarse_width_overhead_le_power (H D p L : ℕ) (hH : 2 ≤ H) (hL : L ≤ H) :
    6 * H ^ p * (L + 1) * (D + 1) * H ^ (8 * D) ≤ H ^ (10 * (D + p + 1)) := by
  have hsix : 6 ≤ H ^ 3 := by
    have hpow := Nat.pow_le_pow_left hH 3
    norm_num at hpow
    omega
  have hlogtwo : L + 1 ≤ H ^ 2 := by nlinarith
  have hdepth : D + 1 ≤ H ^ D :=
    (Nat.succ_le_of_lt (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))).trans
      (Nat.pow_le_pow_left hH D)
  calc
    _ ≤ H ^ 3 * H ^ p * H ^ 2 * H ^ D * H ^ (8 * D) := by gcongr
    _ = H ^ (p + 9 * D + 5) := by
      simp only [← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < H) (by omega)

theorem computedCoarseWidthOverhead_le (N : ℕ) (hN : 0 < N) :
    computedCoarseWidthOverhead N ≤ inputHeight N ^
      (10 * (computedMaxCoarseDepth N + coarseExponent (inputSmallLog N) + 1)) := by
  have hH : 2 ≤ inputHeight N := by
    exact (show 2 ^ 1 ≤ 2 ^ heightExponent N from
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (heightExponent_pos N hN))
  have hlog : Nat.clog 2 N ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
      ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  exact coarse_width_overhead_le_power (inputHeight N) (computedMaxCoarseDepth N)
    (coarseExponent (inputSmallLog N)) (Nat.clog 2 N) hH hlog

theorem computedCoarseWidthOverhead_exp_le (N : ℕ) (hN : 0 < N) :
    (computedCoarseWidthOverhead N : ℝ) ≤ Real.exp (computedCoarseOverheadExponent 10 N) := by
  have h := computedCoarseWidthOverhead_le N hN
  have hcast : (computedCoarseWidthOverhead N : ℝ) ≤ (inputHeight N : ℝ) ^
      (10 * (computedMaxCoarseDepth N + coarseExponent (inputSmallLog N) + 1)) := by exact_mod_cast h
  rw [nat_pow_eq_exp_log (inputHeight N)
    (10 * (computedMaxCoarseDepth N + coarseExponent (inputSmallLog N) + 1))
    (show 0 < inputHeight N from Nat.two_pow_pos (heightExponent N))] at hcast
  convert hcast using 1
  unfold computedCoarseOverheadExponent
  push_cast
  ring

theorem coarse_array_bound_mono (B n L factor : ℝ) (D E : ℕ)
    (hB : 0 ≤ B) (hn : 0 ≤ n) (hL : 0 ≤ L) (hfactor : 1 ≤ factor) (hD : D ≤ E) :
    6 * B * n * L * (D + 1 : ℕ) * factor ^ D ≤
      n * (6 * B * L * (E + 1 : ℕ) * factor ^ E) := by
  have hcount : ((D + 1 : ℕ) : ℝ) ≤ (E + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hD 1
  have hpower := pow_le_pow_right₀ hfactor hD
  calc
    _ ≤ 6 * B * n * L * (E + 1 : ℕ) * factor ^ E := by
      apply mul_le_mul _ hpower (pow_nonneg (by linarith) _) (by positivity)
      exact mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-- The common overhead dominates the actual expected coarse array work
at every source/target interval, including the direct long-target branch. -/
theorem computed_coarse_expected_source_width {α : Type*} [DecidableEq α]
    (N B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (hB : B = (integerParameters N).B) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (x y : List α) (D : ℕ) (hDcomputed : D = computedCoarseDepth N (coarseEntryWidth x y))
    (hsize : coarseEntryWidth x y ≤ N) :
    (∫ draw, (coarseInitialArrayWork B D
      (initialThresholdQ N) (initialLambda N) x y draw : ℝ)
      ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
      (x.length : ℝ) * computedCoarseWidthOverhead N := by
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have hD : D ≤ computedMaxCoarseDepth N :=
    hDcomputed.trans_le (computedCoarseDepth_le_max N (coarseEntryWidth x y) hsize)
  have hcapacity : coarseEntryWidth x y ≤ B ^ D := by
    rw [hB, hDcomputed]
    exact (computed_coarse_depth N _ hN hsize hell).1
  have hHQ : (0 : ℚ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hHR : (1 : ℝ) ≤ inputHeight N := by exact_mod_cast hH
  have hQ : 0 < initialThresholdQ N := pow_pos hHQ 4
  have hlam : 0 < initialLambda N := div_pos (by norm_num) (mul_pos (by norm_num) hHQ)
  have hc := coarseInitialArrayWork_expected_source_width (B := B) (D := D)
    (initialThresholdQ N) (initialLambda N) x y N hsize hcapacity
    hQ hlam ((inputHeight N : ℝ) ^ 8) (one_le_pow₀ hHR) hinverse
  apply hc.trans
  have hm := coarse_array_bound_mono (B : ℝ) (x.length : ℝ) (Nat.clog 2 N + 1 : ℕ)
    ((inputHeight N : ℝ) ^ 8) D (computedMaxCoarseDepth N)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (one_le_pow₀ hHR) hD
  apply hm.trans_eq
  simp only [computedCoarseWidthOverhead, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, hB, ← pow_mul]

end EditApproximation

end OAI
