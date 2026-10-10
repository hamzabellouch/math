import OAI.Probability.InvariantIsing.Arrays.PerturbationFeatures

namespace OAI

/-! Mixed-rotation tensor covariances for Gaussian mean comparison. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

def mixedProjectedOverlap {N : ℕ} (U V : Rotation N) (I : Finset (Fin N))
    (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ I, U (spinVector σ) i * V (spinVector τ) i

lemma mixedProjectedOverlap_abs_le_one {N : ℕ} (U V : Rotation N)
    (I : Finset (Fin N)) (σ τ : Spin N) : |mixedProjectedOverlap U V I σ τ| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => U (spinVector σ) i) (fun i => V (spinVector τ) i)
  have hs : (∑ i ∈ I, U (spinVector σ) i * V (spinVector τ) i) ^ 2 ≤ (N : ℝ) ^ 2 := by
    apply hcs.trans
    simpa only [pow_two] using
      (mul_le_mul (projected_spin_sq_sum_le U I σ) (projected_spin_sq_sum_le V I τ)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  have ha : |∑ i ∈ I, U (spinVector σ) i * V (spinVector τ) i| ≤ N :=
    (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp (by simpa only [sq_abs] using hs)
  unfold mixedProjectedOverlap
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (inv_mul_cancel₀ hn)

lemma mixedProjectedOverlap_sub_first_le {N : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |mixedProjectedOverlap (specialRotation U) (specialRotation W) I σ τ -
      mixedProjectedOverlap (specialRotation V) (specialRotation W) I σ τ| ≤
        frobeniusDistance U V := by
  have he : mixedProjectedOverlap (specialRotation U) (specialRotation W) I σ τ -
      mixedProjectedOverlap (specialRotation V) (specialRotation W) I σ τ =
      (N : ℝ)⁻¹ * ∑ i ∈ I,
        (specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i) *
          specialRotation W (spinVector τ) i := by
    simp only [mixedProjectedOverlap, ← mul_sub, ← Finset.sum_sub_distrib, sub_mul]
  rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (N : ℝ)⁻¹ * (N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left (abs_projected_cross_difference_sum_le U V W I σ τ) (by positivity)
    _ = _ := by field_simp

lemma spectralSpinFeature_mixed_cross {N : ℕ} (U V : Rotation N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    (∑ i : I, spectralSpinFeature U I σ i * spectralSpinFeature V I τ i) =
      mixedProjectedOverlap U V I σ τ := by
  simp only [spectralSpinFeature, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm]
  unfold mixedProjectedOverlap
  congr 1
  exact Finset.sum_coe_sort I (fun i => U (spinVector σ) i * V (spinVector τ) i)

lemma spectralMonomialFeature_mixed_cross {N m : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    (∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature U I d σ v * spectralMonomialFeature V I d τ v) =
      ∏ a, mixedProjectedOverlap U V (I a) σ τ ^ d a := by
  simp only [spectralMonomialFeature, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (v : Fin (d a) → I a) =>
    IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) v *
      IsingPerceptron.tensorFeature (d a) (spectralSpinFeature V (I a) τ) v)]
  simp_rw [IsingPerceptron.tensorFeature_cross, spectralSpinFeature_mixed_cross]

/-- The cross covariance of a tensor increment with any rotated tensor
has a dimension-independent rotation modulus. -/
theorem spectralMonomialFeature_increment_cross_le {N m : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (σ τ : Spin N) :
    |∑ v : SpectralTensorIndex I d,
      (spectralMonomialFeature (specialRotation U) I d σ v -
        spectralMonomialFeature (specialRotation V) I d σ v) *
          spectralMonomialFeature (specialRotation W) I d τ v| ≤
      (∑ a, (d a : ℝ)) * frobeniusDistance U V := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, spectralMonomialFeature_mixed_cross,
    spectralMonomialFeature_mixed_cross]
  have hpow (R : SpecialOrthogonal N) (a : Fin m) :
      |mixedProjectedOverlap (specialRotation R) (specialRotation W) (I a) σ τ ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (mixedProjectedOverlap_abs_le_one _ _ _ _ _)
  calc
    _ ≤ ∑ a, |mixedProjectedOverlap (specialRotation U) (specialRotation W) (I a) σ τ ^ d a -
        mixedProjectedOverlap (specialRotation V) (specialRotation W) (I a) σ τ ^ d a| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _ (fun a _ => hpow U a) (fun a _ => hpow V a)
    _ ≤ ∑ a, (d a : ℝ) * frobeniusDistance U V := by
      apply Finset.sum_le_sum
      intro a _
      exact (abs_pow_sub_pow_le_degree (mixedProjectedOverlap_abs_le_one _ _ _ _ _)
        (mixedProjectedOverlap_abs_le_one _ _ _ _ _) (d a)).trans
        (mul_le_mul_of_nonneg_left (mixedProjectedOverlap_sub_first_le hN U V W (I a) σ τ)
          (Nat.cast_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI
