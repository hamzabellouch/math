import OAI.Geometry.RCD.Harmonic.EuclideanAffineImprovement

namespace OAI

/-! # A single strict affine contraction for all normalized harmonic models -/

open Set Metric
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The Euclidean derivative estimate chooses the dyadic scale before
any harmonic function, working radius, or RCD sequence is chosen. -/
theorem EuclideanHarmonicHessianInput.affine_contraction {n : ℕ}
    (hinput : EuclideanHarmonicHessianInput n) :
    ∃ m : ℕ, 3 ≤ m ∧ ∀ S : ℝ, 0 < S →
      let θ := (1 / 2 : ℝ) ^ m
      ∀ w : EuclideanHarmonicModel n S,
        ∃ (c : ℝ) (v : Euclidean n), ∃ hρS : θ * S ≤ S,
          ‖∑ i, affineErrorCoefficients c (fun j => v j) i • w.moments hρS i‖ <
            (1 / 4 : ℝ) * θ * Real.sqrt θ := by
  obtain ⟨C, hC, hbound⟩ := hinput
  obtain ⟨m, hm, hscale⟩ := exists_dyadic_affine_contraction C
  refine ⟨m, hm, ?_⟩
  intro S hS θ w
  have hθ : 0 < θ := pow_pos (by norm_num) _
  have hθhalf : θ ≤ 1 / 2 := by
    have hh : θ = (1 / 2 : ℝ) ^ (m - 1) * (1 / 2) := by
      dsimp only [θ]
      rw [← pow_succ]
      congr 1
      omega
    rw [hh]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hρ : 0 < θ * S := mul_pos hθ hS
  have hhalf : θ * S ≤ S / 2 := by nlinarith
  have hρS : θ * S ≤ S := by linarith
  obtain ⟨c, v, hcv⟩ := w.affine_candidate hS hρ hhalf
    (div_nonneg hC.le (sq_nonneg S)) (hbound S hS w)
  refine ⟨c, v, hρS, ?_⟩
  have heq : C / S ^ 2 * (θ * S) ^ 2 = C * θ ^ 2 := by
    field_simp
  exact lt_of_le_of_lt (hcv.trans_eq heq) hscale

end RegularPointCoordinates

end

end OAI
