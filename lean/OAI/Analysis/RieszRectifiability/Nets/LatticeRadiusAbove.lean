import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.AnnularLatticeScales

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem exists_lattice_radius_above (R : ℝ) (k : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (htop : δ ≤ latticeRadius R k) :
    ∃ t : ℕ, δ ≤ latticeRadius R (k + t) ∧ latticeRadius R (k + t) ≤ 64 * δ := by
  let N := annularLatticeDepth R k (8 * δ) (by positivity)
  have hN : latticeRadius R (k + N) ≤ δ := by
    have hu := annularLatticeDepth_radius_upper R k (8 * δ) (by positivity)
    change latticeRadius R (k + N) ≤ (8 * δ) / 8 at hu
    linarith
  by_cases hz : N = 0
  · refine ⟨0, by simpa only [Nat.add_zero] using! htop, ?_⟩
    rw [hz, Nat.add_zero] at hN
    simp only [Nat.add_zero]
    linarith
  · have hlow : δ < latticeRadius R (k + (N - 1)) := by
      by_contra hbad
      have hm := annularLatticeDepth_minimal R k (8 * δ) (by positivity) (N - 1)
        (by linarith [le_of_not_gt hbad])
      change N ≤ N - 1 at hm
      omega
    have hscale : latticeRadius R (k + (N - 1)) = 64 * latticeRadius R (k + N) := by
      rw [show k + N = (k + (N - 1)) + 1 by omega, latticeRadius_succ]
      ring
    refine ⟨N - 1, hlow.le, ?_⟩
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hN (by norm_num)

end

end RieszRectifiability

end OAI
