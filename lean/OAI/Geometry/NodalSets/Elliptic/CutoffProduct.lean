import Mathlib.Data.Nat.Choose.Sum
import OAI.Geometry.NodalSets.Elliptic.SmoothCutoff

namespace OAI

namespace Yau.Waves
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smul_derivative_power_bound {beta : E → ℝ} {u : E → F}
    (hb : ContDiff ℝ ∞ beta) (hu : ContDiff ℝ ∞ u)
    (k : ℕ) (x : E) {B A N w : ℝ} (hB : 0 ≤ B) (_ : 0 ≤ A)
    (hN : 0 ≤ N) (_ : 0 ≤ w)
    (hbeta : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j beta x‖ ≤ B * N ^ j)
    (hwave : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ A * N ^ j * w) :
    ‖iteratedFDeriv ℝ k (fun z ↦ beta z • u z) x‖ ≤
      (2 : ℝ) ^ k * B * A * N ^ k * w := by
  have hle := norm_iteratedFDeriv_smul_le hb hu x (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := hle
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (B * A * N ^ k * w) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have hm := mul_le_mul (hbeta j hjk) (hwave (k - j) (Nat.sub_le _ _))
        (norm_nonneg _) (mul_nonneg hB (pow_nonneg hN _))
      have he : (B * N ^ j) * (A * N ^ (k - j) * w) = B * A * N ^ k * w := by
        rw [show (B * N ^ j) * (A * N ^ (k - j) * w) =
          B * A * (N ^ j * N ^ (k - j)) * w by ring, ← pow_add, Nat.add_sub_of_le hjk]
      rw [he] at hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (k.choose j))
    _ = _ := by
      rw [← Finset.sum_mul]
      have he : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [he]
      ring

variable [FiniteDimensional ℝ E]

theorem scaledCutoff_all_derivatives (k : ℕ) :
    ∃ B > 0, ∀ j, j ≤ k → ∀ N : ℝ, 1 ≤ N → ∀ y x : E,
      ‖iteratedFDeriv ℝ j (scaledCutoff N y) x‖ ≤ B * N ^ j := by
  choose C hC hbound using (fun j ↦ scaledCutoff_derivative_bound (E := E) j)
  let B := ∑ j ∈ Finset.range (k + 1), C j
  have hjB (j : ℕ) (hj : j ≤ k) : C j ≤ B :=
    Finset.single_le_sum (fun i _ ↦ (hC i).le) (Finset.mem_range.mpr (by omega))
  refine ⟨B, (hC 0).trans_le (hjB 0 (Nat.zero_le _)), ?_⟩
  intro j hj N hN y x
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ C j * N ^ ((j : ℝ) / 3) := hbound j N hpos y x
    _ ≤ B * N ^ ((j : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right (hjB j hj) (Real.rpow_nonneg hpos.le _)
    _ ≤ B * N ^ j := by
      rw [← Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_left _ ((hC 0).trans_le (hjB 0 (Nat.zero_le _))).le
      exact Real.rpow_le_rpow_of_exponent_le hN (by have := Nat.cast_nonneg (α := ℝ) j; linarith)

theorem cutoff_preserves_derivative_exponent (k : ℕ) :
    ∃ B > 0, ∀ N : ℝ, 1 ≤ N → ∀ y x : E, ∀ u : E → F,
      ContDiff ℝ ∞ u → ∀ A w : ℝ, 0 ≤ A → 0 ≤ w →
      (∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ A * N ^ j * w) →
      ‖iteratedFDeriv ℝ k (fun z ↦ scaledCutoff N y z • u z) x‖ ≤
        (2 : ℝ) ^ k * B * A * N ^ k * w := by
  obtain ⟨B, hB, hb⟩ := scaledCutoff_all_derivatives (E := E) k
  refine ⟨B, hB, ?_⟩
  intro N hN y x u hu A w hA hw hbound
  exact smul_derivative_power_bound (scaledCutoff_contDiff N y) hu k x hB.le hA
    (le_trans zero_le_one hN) hw (fun j hj ↦ hb j hj N hN y x) hbound

end
end Yau.Waves

end OAI
