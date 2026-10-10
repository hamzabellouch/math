import OAI.NumberTheory.Ostmann.ZeroDensity.DensityBlockCauchy

namespace OAI

/-! # Summing finitely many actual polynomial blocks -/

namespace Ostmann

open scoped BigOperators

 theorem density_finite_block_square {ι : Type*} (R : Finset ι) (J : ℕ) (f : ι → ℕ → ℂ) :
    (∑ i ∈ R, ‖∑ j ∈ Finset.range J, f i j‖ ^ 2) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, ∑ i ∈ R, ‖f i j‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ R, (J : ℝ) * ∑ j ∈ Finset.range J, ‖f i j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa using density_weighted_sum_norm_sq (Finset.range J) (f i) (fun _ => (1 : ℝ))
        (fun _ _ => by norm_num)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end Ostmann

end OAI
