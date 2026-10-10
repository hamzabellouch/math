import OAI.Probability.InvariantIsing.Gaussian.GaussianNormMoments
import OAI.Probability.InvariantIsing.Spectral.HermitianEigenvalueRoots
import OAI.Probability.InvariantIsing.Pressure.RandomSpectralMeasurability

namespace OAI

/-! The actual Gram eigenvalues are bounded by the squared rectangular operator norm. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace InvariantIsing

lemma gaussianPatternCoupling_norm_le {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternCoupling 1 z‖ ≤ (gaussianPatternSingularMax z)^2/N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : ‖(gaussianPatternArray z)ᵀ‖ = ‖gaussianPatternArray z‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (gaussianPatternArray z)
  have he : ‖gaussianPatternArray z‖ = gaussianPatternSingularMax z := rfl
  calc
    _ = |1/(N : ℝ)| * ‖gaussianPatternArray z*(gaussianPatternArray z)ᵀ‖ := by
      rw [gaussianPatternCoupling,norm_smul,Real.norm_eq_abs]
    _ ≤ (1/(N : ℝ))*(‖gaussianPatternArray z‖*‖gaussianPatternArray z‖) := by
      rw [abs_of_pos (one_div_pos.mpr hN')]
      exact mul_le_mul_of_nonneg_left ((Matrix.l2_opNorm_mul _ _).trans_eq (by rw [ht]))
        (by positivity)
    _ = _ := by rw [he]; ring

lemma gaussianPatternEigenvalues_abs_le {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (i : Fin N) :
    |gaussianPatternEigenvalues z i| ≤ (gaussianPatternSingularMax z)^2/N := by
  apply le_trans _ (gaussianPatternCoupling_norm_le hN z)
  unfold gaussianPatternEigenvalues Matrix.IsHermitian.eigenvalues
  exact hermitian_eigenvalues₀_norm_le _ _ _

lemma gaussianPattern_spectralRadius_le {n m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) :
    spectralRadius (fun i => c*gaussianPatternEigenvalues z i) ≤
      |c| * (gaussianPatternSingularMax z)^2/(n+1) := by
  apply (spectralRadius_le_iff _ _).mpr
  intro i
  rw [abs_mul,mul_div_assoc]
  simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
    mul_le_mul_of_nonneg_left (gaussianPatternEigenvalues_abs_le (Nat.succ_pos n) z i) (abs_nonneg c)

end InvariantIsing

end

end OAI
