import OAI.Probability.InvariantIsing.Arrays.OverlapBounds

namespace OAI

/-! Finite-rank overlap errors in cavity coordinates. The retained
coordinates cancel exactly; the error is controlled by the special
projections and the fixed number of added spins. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityCoordinatePairing {d : ℕ} (U : Rotation d) (I : Finset (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ I, U x i * U y i

lemma cavityCoordinatePairing_abs_le {d : ℕ} (U : Rotation d) (I : Finset (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    |cavityCoordinatePairing U I x y| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have hx : (∑ i ∈ I, (U x i) ^ 2) ≤ ‖x‖ ^ 2 := by
    rw [← U.norm_map x, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => sq_nonneg _)
  have hy : (∑ i ∈ I, (U y i) ^ 2) ≤ ‖y‖ ^ 2 := by
    rw [← U.norm_map y, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ I, |U x i * U y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, ((U x i) ^ 2 + (U y i) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [sq_nonneg (|U x i| - |U y i|), sq_abs (U x i), sq_abs (U y i)]
    _ = ((∑ i ∈ I, (U x i) ^ 2) + ∑ i ∈ I, (U y i) ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

def cavityJoinVector {d n : ℕ} (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    EuclideanSpace ℝ (Fin (d + n)) :=
  WithLp.toLp 2 (Fin.append (fun i => y i) (fun j => spinValue (ε j)))

lemma cavityJoinVector_norm_sq {d n : ℕ} (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    ‖cavityJoinVector y ε‖ ^ 2 = ‖y‖ ^ 2 + n := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add, EuclideanSpace.real_norm_sq_eq]
  simp [cavityJoinVector]

lemma cavity_small_overlap_difference {d n : ℕ}
    (U : Rotation (d + n)) (V : Rotation d)
    (I : Finset (Fin (d + n))) (J : Finset (Fin d))
    (y₁ y₂ : EuclideanSpace ℝ (Fin d)) (ε₁ ε₂ : Spin n) :
    |cavityCoordinatePairing U I (cavityJoinVector y₁ ε₁) (cavityJoinVector y₂ ε₂) -
      cavityCoordinatePairing V J y₁ y₂| ≤ ‖y₁‖ ^ 2 + ‖y₂‖ ^ 2 + n := by
  have hfull := cavityCoordinatePairing_abs_le U I (cavityJoinVector y₁ ε₁)
    (cavityJoinVector y₂ ε₂)
  have hbase := cavityCoordinatePairing_abs_le V J y₁ y₂
  rw [cavityJoinVector_norm_sq, cavityJoinVector_norm_sq] at hfull
  have h := (abs_sub _ _).trans (add_le_add hfull hbase)
  linarith

lemma cavity_normalized_overlap_error_sharp {N n : ℕ} (hN : 0 < N)
    (retained fullSmall baseSmall B : ℝ)
    (hsmall : |fullSmall - baseSmall| ≤ B)
    (hbase : |(retained + baseSmall) / N| ≤ 1) :
    |(retained + fullSmall) / (N + n : ℕ) - (retained + baseSmall) / N| ≤
      (B + n) / (N + n : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNn : (0 : ℝ) < N + n := by positivity
  have he : (retained + fullSmall) / (N + n : ℕ) - (retained + baseSmall) / N =
      (fullSmall - baseSmall) / (N + n : ℝ) -
        ((n : ℝ) / (N + n)) * ((retained + baseSmall) / N) := by
    push_cast
    field_simp
    ring
  rw [he]
  calc
    _ ≤ |(fullSmall - baseSmall) / (N + n : ℝ)| +
        |((n : ℝ) / (N + n)) * ((retained + baseSmall) / N)| := abs_sub _ _
    _ ≤ B / (N + n) + (n : ℝ) / (N + n) := by
      rw [abs_div, abs_of_pos hNn, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / (N + n))]
      exact add_le_add (div_le_div_of_nonneg_right hsmall hNn.le)
        ((mul_le_mul_of_nonneg_left hbase (by positivity)).trans_eq (mul_one _))
    _ = (B + n) / (N + n) := (add_div _ _ _).symm

lemma cavity_normalized_overlap_error {N n : ℕ} (hN : 0 < N)
    (retained fullSmall baseSmall B : ℝ) (hB : 0 ≤ B)
    (hsmall : |fullSmall - baseSmall| ≤ B)
    (hbase : |(retained + baseSmall) / N| ≤ 1) :
    |(retained + fullSmall) / (N + n : ℕ) - (retained + baseSmall) / N| ≤
      (B + n) / N := by
  exact (cavity_normalized_overlap_error_sharp (n := n) hN retained fullSmall baseSmall B hsmall hbase).trans
    (div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hN) (le_add_of_nonneg_right (Nat.cast_nonneg n)))

/-- The local spectral-overlap comparison used in the perturbation
interpolation, with a constant depending only on the cavity size. -/
theorem cavity_overlap_error {N d n : ℕ} (hN : 0 < N)
    (retained : ℝ) (U : Rotation (d + n)) (V : Rotation d)
    (I : Finset (Fin (d + n))) (J : Finset (Fin d))
    (y₁ y₂ : EuclideanSpace ℝ (Fin d)) (ε₁ ε₂ : Spin n)
    (hbase : |(retained + cavityCoordinatePairing V J y₁ y₂) / N| ≤ 1) :
    |(retained + cavityCoordinatePairing U I (cavityJoinVector y₁ ε₁) (cavityJoinVector y₂ ε₂)) /
        (N + n : ℕ) - (retained + cavityCoordinatePairing V J y₁ y₂) / N| ≤
      ((2 * (n : ℝ) + 1) / N) * (1 + ‖y₁‖ ^ 2 + ‖y₂‖ ^ 2) := by
  have h := cavity_normalized_overlap_error (n := n) hN retained _ _
    (‖y₁‖ ^ 2 + ‖y₂‖ ^ 2 + n) (by positivity)
    (cavity_small_overlap_difference U V I J y₁ y₂ ε₁ ε₂) hbase
  apply h.trans
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hn.le
  nlinarith [sq_nonneg ‖y₁‖, sq_nonneg ‖y₂‖,
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖y₁‖),
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖y₂‖)]

/-- Appending `n` spins changes the total overlap by at most `2n/(N+n)`. -/
theorem cavity_total_overlap_extension {N n : ℕ} (hN : 0 < N)
    (σ₁ σ₂ : Spin N) (ε₁ ε₂ : Spin n) :
    |(∑ i : Fin (N + n), spinValue (Fin.append σ₁ ε₁ i) *
        spinValue (Fin.append σ₂ ε₂ i)) / (N + n : ℕ) -
      (∑ i : Fin N, spinValue (σ₁ i) * spinValue (σ₂ i)) / N| ≤
        2 * (n : ℝ) / (N + n) := by
  have hsum {k : ℕ} (x y : Spin k) : |∑ i, spinValue (x i) * spinValue (y i)| ≤ k := by
    calc
      _ ≤ ∑ i, |spinValue (x i) * spinValue (y i)| := Finset.abs_sum_le_sum_abs _ _
      _ = k := by simp [abs_mul]
  have hbase : |((∑ i : Fin N, spinValue (σ₁ i) * spinValue (σ₂ i)) + 0) / N| ≤ 1 := by
    rw [add_zero, abs_div, abs_of_pos (show (0 : ℝ) < (N : ℝ) from Nat.cast_pos.mpr hN)]
    exact (div_le_one (Nat.cast_pos.mpr hN)).mpr (hsum σ₁ σ₂)
  have h := cavity_normalized_overlap_error_sharp (n := n) hN
    (∑ i : Fin N, spinValue (σ₁ i) * spinValue (σ₂ i))
    (∑ i : Fin n, spinValue (ε₁ i) * spinValue (ε₂ i)) 0 n
    (by simpa only [sub_zero] using hsum ε₁ ε₂) hbase
  simpa only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, add_zero, two_mul] using h

end InvariantIsing

end

end OAI
