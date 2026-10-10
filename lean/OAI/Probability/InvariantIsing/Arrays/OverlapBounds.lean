import OAI.Probability.InvariantIsing.Arrays.Overlaps
import OAI.Probability.InvariantIsing.Pressure.PressureLipschitz

namespace OAI

/-! Dimension-independent bounds for projected spectral overlap kernels. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma projected_spin_sq_sum_le {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ : Spin N) :
    (∑ i ∈ I, U (spinVector σ) i ^ 2) ≤ N := by
  rw [← rotated_spin_sq_sum U σ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun _ _ _ => sq_nonneg _)

lemma projectedOverlap_abs_le_one {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |projectedOverlap U I σ τ| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => U (spinVector σ) i) (fun i => U (spinVector τ) i)
  have hs : (∑ i ∈ I, U (spinVector σ) i * U (spinVector τ) i) ^ 2 ≤ (N : ℝ) ^ 2 := by
    apply hcs.trans
    simpa only [pow_two] using
      (mul_le_mul (projected_spin_sq_sum_le U I σ) (projected_spin_sq_sum_le U I τ)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  have ha : |∑ i ∈ I, U (spinVector σ) i * U (spinVector τ) i| ≤ N :=
    (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp (by simpa only [sq_abs] using hs)
  unfold projectedOverlap
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (inv_mul_cancel₀ hn)

lemma projectedOverlap_self_le_one {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ : Spin N) :
    projectedOverlap U I σ σ ≤ 1 :=
  (le_abs_self _).trans (projectedOverlap_abs_le_one U I σ σ)

lemma abs_projected_cross_difference_sum_le {N : ℕ}
    (U V W : SpecialOrthogonal N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |∑ i ∈ I, (specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i) *
      specialRotation W (spinVector τ) i| ≤ N * frobeniusDistance U V := by
  let d := frobeniusDistance U V
  let x := fun i => specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i
  let y := fun i => specialRotation W (spinVector τ) i
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hx : (∑ i ∈ I, x i ^ 2) ≤ N * d ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => sq_nonneg _)).trans (specialRotation_spin_dist_sq_le U V σ)
  have hy : (∑ i ∈ I, y i ^ 2) ≤ N := projected_spin_sq_sum_le _ I τ
  have hsq : (∑ i ∈ I, x i * y i) ^ 2 ≤ ((N : ℝ) * d) ^ 2 := by
    calc
      _ ≤ (∑ i ∈ I, x i ^ 2) * ∑ i ∈ I, y i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq I x y
      _ ≤ ((N : ℝ) * d ^ 2) * N := mul_le_mul hx hy
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

/-- Every projected overlap has a uniform Frobenius Lipschitz constant. This
controls the covariances of the Gaussian GG perturbations. -/
theorem abs_projectedOverlap_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (U V : SpecialOrthogonal N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |projectedOverlap (specialRotation U) I σ τ - projectedOverlap (specialRotation V) I σ τ| ≤
      2 * frobeniusDistance U V := by
  let A := ∑ i ∈ I, (specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i) *
    specialRotation U (spinVector τ) i
  let B := ∑ i ∈ I, (specialRotation U (spinVector τ) i - specialRotation V (spinVector τ) i) *
    specialRotation V (spinVector σ) i
  have hA : |A| ≤ N * frobeniusDistance U V := abs_projected_cross_difference_sum_le U V U I σ τ
  have hB : |B| ≤ N * frobeniusDistance U V := abs_projected_cross_difference_sum_le U V V I τ σ
  have he : projectedOverlap (specialRotation U) I σ τ - projectedOverlap (specialRotation V) I σ τ =
      (N : ℝ)⁻¹ * (A + B) := by
    unfold projectedOverlap
    rw [← mul_sub]
    congr 1
    dsimp only [A, B]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : |A + B| ≤ 2 * N * frobeniusDistance U V := by
    have h := (abs_add_le A B).trans (add_le_add hA hB)
    linarith
  rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (N : ℝ)⁻¹ * (2 * N * frobeniusDistance U V) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

end InvariantIsing

end

end OAI
