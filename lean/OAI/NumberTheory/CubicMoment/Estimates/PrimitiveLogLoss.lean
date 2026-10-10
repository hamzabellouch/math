import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveRetainedMoment
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerMoments

namespace OAI

/-! The exact dyadic and ramified losses cost an arbitrarily small power. -/
noncomputable section
namespace CubicFirstMoment

theorem primitive_moment_log_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*ramifiedMomentLoss J ≤
        C*(2*J)^ε := by
  obtain ⟨C,hC,hbound⟩ := natLog_power_bound (2+2*ramifiedIdealPrimes.card) hε
  refine ⟨C,hC,?_⟩
  intro J hJ
  have hJ0 : 0 ≤ 2*J := by linarith
  have hn : 1 ≤ ⌊2*J⌋₊ := (Nat.one_le_floor_iff (2*J)).mpr (by linarith)
  have hc : (idealDyadIndices (fullIdealBall J)).card ≤ Nat.log 2 ⌊2*J⌋₊+1 :=
    idealDyadIndices_card_le _ (fun ν hν => (mem_fullIdealBall.mp hν).trans (by linarith))
  let L : ℝ := (Nat.log 2 ⌊2*J⌋₊+1:ℕ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hc' : ((idealDyadIndices (fullIdealBall J)).card:ℝ) ≤ L := by
    dsimp [L]
    exact_mod_cast hc
  calc
    _ ≤ L^2*(L^ramifiedIdealPrimes.card)^2 := by
      dsimp only [ramifiedMomentLoss]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hc' 2) (sq_nonneg _)
    _ = L^(2+2*ramifiedIdealPrimes.card) := by
      rw [← pow_mul,← pow_add]
      congr 1
      omega
    _ ≤ C*(⌊2*J⌋₊:ℝ)^ε := hbound _ hn
    _ ≤ C*(2*J)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hJ0) hε.le) hC.le

theorem primitive_moment_weighted_log_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N J : ℝ, 1 ≤ N → 1 ≤ J →
      (((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*ramifiedMomentLoss J)*
        (N*(2*J))^(ε/2) ≤ C*(N*(2*J))^ε := by
  obtain ⟨C,hC,hbound⟩ := primitive_moment_log_loss (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro N J hN hJ
  have hJ0 : 0 < 2*J := by linarith
  have hQ : 0 < N*(2*J) := mul_pos (zero_lt_one.trans_le hN) hJ0
  calc
    _ ≤ (C*(2*J)^(ε/2))*(N*(2*J))^(ε/2) :=
      mul_le_mul_of_nonneg_right (hbound J hJ) (Real.rpow_nonneg hQ.le _)
    _ ≤ (C*(N*(2*J))^(ε/2))*(N*(2*J))^(ε/2) := by
      have hp : (2*J)^(ε/2) ≤ (N*(2*J))^(ε/2) := Real.rpow_le_rpow hJ0.le
        (le_mul_of_one_le_left hJ0.le hN) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le)
        (Real.rpow_nonneg hQ.le _)
    _ = C*(N*(2*J))^ε := by
      rw [mul_assoc,← Real.rpow_add hQ]
      congr 2
      ring

end CubicFirstMoment

end

end OAI
