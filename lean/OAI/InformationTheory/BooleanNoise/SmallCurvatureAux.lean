import OAI.InformationTheory.BooleanNoise.EntropySeries

namespace OAI

namespace LeanBlast.CourtadeKumar

theorem artanh_le_cubic_tail {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2
  have huabs : |u| < 1 := by rwa [abs_of_nonneg hu0]
  have hu2 : u ^ 2 < 1 := by nlinarith [sq_nonneg (u - 1)]
  have hseries := hasSum_artanh huabs
  have htail : HasSum
      (fun k : ℕ => u ^ (2 * (k + 1) + 1) / (2 * ((k + 1 : ℕ) : ℝ) + 1))
      (Real.artanh u - u) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hseries
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left (u ^ 3 / 3)
  have hle : Real.artanh u - u ≤ (u ^ 3 / 3) * (1 - u ^ 2)⁻¹ := by
    apply hasSum_le _ htail hgeom
    intro k
    have hpow : u ^ (2 * (k + 1) + 1) = u ^ 3 * (u ^ 2) ^ k := by
      rw [show 2 * (k + 1) + 1 = 3 + 2 * k by omega, pow_add, pow_mul]
    rw [hpow]
    calc
      _ ≤ (u ^ 3 * (u ^ 2) ^ k) / 3 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      _ = _ := by ring
  calc
    Real.artanh u = u + (Real.artanh u - u) := by ring
    _ ≤ u + (u ^ 3 / 3) * (1 - u ^ 2)⁻¹ := by linarith
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem cubic_le_artanh {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    u + u ^ 3 / 3 ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu.1 hu.2 2
  norm_num [Finset.sum_range_succ] at h
  exact h

end LeanBlast.CourtadeKumar

end OAI
