import OAI.Analysis.Cotype.Fourier
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fourier_mass_le {f : (ι → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ ε, |f ε| ≤ M) :
    (∑ p, fourier f p ^ 2) ≤ M ^ 2 := by
  rw [parseval]
  have hsq (ε : ι → Bool) : f ε ^ 2 ≤ M ^ 2 := by
    simpa using (sq_le_sq₀ (abs_nonneg (f ε)) hM).2 (hf ε)
  unfold average
  rw [smul_eq_mul]
  calc
    _ ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ _ : ι → Bool, M ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ε _ => hsq ε))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = M ^ 2 := by simp

theorem fourier_subset_mass_le {f : (ι → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ ε, |f ε| ≤ M) (s : Finset (ι → Bool)) :
    (∑ p ∈ s, fourier f p ^ 2) ≤ M ^ 2 := by
  apply le_trans _ (fourier_mass_le hM hf)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun p _ _ => sq_nonneg (fourier f p))

theorem fourier_subset_sum_bound {f : (ι → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ ε, |f ε| ≤ M) (s : Finset (ι → Bool)) :
    |∑ p ∈ s, fourier f p| ≤ M * Real.sqrt s.card := by
  have hcs : (∑ p ∈ s, fourier f p) ^ 2 ≤
      (s.card : ℝ) * ∑ p ∈ s, fourier f p ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fourier f)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg s.card)]
  exact hcs.trans (by simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (fourier_subset_mass_le hM hf s) (Nat.cast_nonneg s.card))

end Cotype

end

end OAI
