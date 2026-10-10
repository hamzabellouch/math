import OAI.Probability.FreeIsing.Estimates.NonbacktrackingLiftBound
import OAI.Probability.FreeIsing.Estimates.NonbacktrackingOperator
import OAI.Probability.FreeIsing.Spectral.RealChebyshevBound

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

section Generic

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

def vertexRate (q : ℝ) : ℝ := 2 * q / (1 + q ^ 2)

theorem vertexRate_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ vertexRate q := by
  unfold vertexRate
  positivity

theorem vertexRate_lt_one {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    vertexRate q < 1 := by
  unfold vertexRate
  apply (div_lt_one (by positivity : 0 < 1 + q ^ 2)).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr hq1)]

def normalizedVertex (q : ℝ) (A : E →L[𝕜] E) : E →L[𝕜] E :=
  ((1 + q ^ 2) / (2 * q)) • A

def normalizedCompanion (q : ℝ) (A : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  nonbacktrackingOperator (normalizedVertex q A)
    (algebraMap ℝ (E →L[𝕜] E) q) (algebraMap ℝ (E →L[𝕜] E) q⁻¹)

def companion (q : ℝ) (A : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  q • normalizedCompanion q A

theorem normalizedVertex_selfAdjoint (q : ℝ) (A : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (normalizedVertex q A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner 𝕜 (((1 + q ^ 2) / (2 * q) : ℝ) • A x) y =
    inner 𝕜 x (((1 + q ^ 2) / (2 * q) : ℝ) • A y)
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_real_left,
    inner_smul_real_right]
  congr 1
  exact hA.isSymmetric x y

omit [CompleteSpace E] in
theorem norm_normalizedVertex_le_one {q : ℝ} (hq : 0 < q)
    (A : E →L[𝕜] E) (hA : ‖A‖ ≤ vertexRate q) :
    ‖normalizedVertex q A‖ ≤ 1 := by
  have hscalar : 0 ≤ (1 + q ^ 2) / (2 * q) := by positivity
  rw [normalizedVertex, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar]
  calc
    (1 + q ^ 2) / (2 * q) * ‖A‖ ≤ (1 + q ^ 2) / (2 * q) * vertexRate q :=
      mul_le_mul_of_nonneg_left hA hscalar
    _ = 1 := by unfold vertexRate; field_simp

omit [CompleteSpace E] in
theorem companion_apply {q : ℝ} (hq : q ≠ 0) (A : E →L[𝕜] E) (x y : E) :
    companion q A (x, y) = (-(q ^ 2 : ℝ) • y, x + (1 + q ^ 2) • A y) := by
  have hscalar : q * ((1 + q ^ 2) / (2 * q)) +
      q * ((1 + q ^ 2) / (2 * q)) = 1 + q ^ 2 := by field_simp; ring
  simp only [companion, normalizedCompanion, smul_apply,
    nonbacktrackingOperator_apply, ContinuousLinearMap.algebraMap_apply,
    normalizedVertex, Prod.smul_mk, smul_add, smul_neg, smul_smul]
  rw [mul_inv_cancel₀ hq, one_smul, add_assoc, ← add_smul, hscalar]
  congr 1
  rw [pow_two, neg_smul]

omit [CompleteSpace E] in
theorem norm_normalizedCompanion_pow_le_of_chebyshev_bound {q : ℝ} (hq : 0 < q)
    (A : E →L[𝕜] E) (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) :
    ‖normalizedCompanion q A ^ n‖ ≤ (‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) := by
  have hcd : algebraMap ℝ (E →L[𝕜] E) q *
      algebraMap ℝ (E →L[𝕜] E) q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq.ne', map_one]
  have hdc : algebraMap ℝ (E →L[𝕜] E) q⁻¹ *
      algebraMap ℝ (E →L[𝕜] E) q = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq.ne', map_one]
  have hcB := Algebra.commutes (A := E →L[𝕜] E) q (normalizedVertex q A)
  cases n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_add, mul_one]
      exact ContinuousLinearMap.norm_id_le.trans (by
        linarith [ContinuousLinearMap.opNorm_nonneg (normalizedCompanion q A)])
  | succ n =>
      have h := norm_nonbacktrackingOperator_pow_le hcd hdc hcB hU n
      change ‖normalizedCompanion q A ^ (n + 1)‖ ≤
        ((n : ℝ) + 1) * ‖normalizedCompanion q A‖ + n at h
      simp only [Nat.cast_succ]
      nlinarith [norm_nonneg (normalizedCompanion q A)]

omit [CompleteSpace E] in
theorem norm_companion_pow_le_of_chebyshev_bound {q : ℝ} (hq : 0 < q)
    (A : E →L[𝕜] E) (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) :
    ‖companion q A ^ n‖ ≤
      (‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) * q ^ n := by
  rw [companion, smul_pow]
  calc
    ‖q ^ n • normalizedCompanion q A ^ n‖ ≤
        ‖q ^ n‖ * ‖normalizedCompanion q A ^ n‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ = q ^ n * ‖normalizedCompanion q A ^ n‖ := by
      rw [Real.norm_eq_abs, abs_pow, abs_of_pos hq]
    _ ≤
        q ^ n * ((‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (norm_normalizedCompanion_pow_le_of_chebyshev_bound hq A hU n)
        (pow_nonneg hq.le n)
    _ = _ := by ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem exists_norm_edgeOperator_pow_bound_of_chebyshev_bound {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hAnorm : ‖A‖ ≤ vertexRate q)
    (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖edgeOperator (1 + q ^ 2) (q ^ 2)
        F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
          K * ((n : ℝ) + 1) * q ^ n := by
  let L : ℝ := ‖F.toContinuousLinearMap.coprod H.toContinuousLinearMap‖ /
    Real.sqrt (1 - vertexRate q)
  let C : ℝ := L * (‖normalizedCompanion q A‖ + 1)
  have hL : 0 ≤ L := div_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := mul_nonneg hL (by positivity)
  refine ⟨C + 1, by positivity, ?_⟩
  intro n
  have hT : ∀ x y, companion q A (x, y) =
      (-((q ^ 2 : ℝ) : 𝕜) • y, x + ((1 + q ^ 2 : ℝ) : 𝕜) • A y) := by
    intro x y
    simpa only [RCLike.real_smul_eq_coe_smul (K := 𝕜), map_neg] using
      companion_apply hq.ne' A x y
  have hbound := norm_edgeOperator_pow_le_of_companion_bound
    (1 + q ^ 2) (q ^ 2) (sq_nonneg q) (by ring)
    F H J A (vertexRate_nonneg hq.le) (vertexRate_lt_one hq hq1)
    hAnorm hFH hJF hJH (companion q A) hT n
    (norm_companion_pow_le_of_chebyshev_bound hq A hU n)
  apply hbound.trans
  apply max_le
  · change L * ((‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) * q ^ n) ≤ _
    change _ ≤ (L * (‖normalizedCompanion q A‖ + 1) + 1) * ((n : ℝ) + 1) * q ^ n
    nlinarith [pow_nonneg hq.le n, mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)
      (pow_nonneg hq.le n)]
  · have hpow : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1.le
    have hpow0 : 0 ≤ q ^ n := pow_nonneg hq.le n
    have hsq : (q ^ 2) ^ n ≤ q ^ n := by
      rw [pow_two, mul_pow]
      nlinarith
    apply hsq.trans
    have hcoef : 1 ≤ (C + 1) * ((n : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hpow0

theorem summable_norm_edgeOperator_pow_of_chebyshev_bound {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hAnorm : ‖A‖ ≤ vertexRate q)
    (hU : ∀ n : ℕ, ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    Summable (fun n : ℕ => ‖edgeOperator (1 + q ^ 2) (q ^ 2)
      F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖) := by
  obtain ⟨K, _, hK⟩ := exists_norm_edgeOperator_pow_bound_of_chebyshev_bound hq hq1 F H J A
    hAnorm hU hFH hJF hJH
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    simpa only [pow_one, add_mul, one_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm).add
        (summable_geometric_of_norm_lt_one hqnorm)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) hK
  simpa only [mul_assoc] using hs.mul_left K

end Generic

section Complex
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem normalizedVertex_chebyshev_bound {q : ℝ} (hq : 0 < q)
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (n : ℕ) : ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    rw [ContinuousLinearMap.opNorm_subsingleton]
    positivity
  · let := hE
    exact norm_aeval_chebyshev_U_le n (normalizedVertex_selfAdjoint q A hA)
      (norm_normalizedVertex_le_one hq A hAnorm)

theorem norm_normalizedCompanion_pow_le {q : ℝ} (hq : 0 < q)
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (n : ℕ) :
    ‖normalizedCompanion q A ^ n‖ ≤ (‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) := by
  exact norm_normalizedCompanion_pow_le_of_chebyshev_bound hq A
    (normalizedVertex_chebyshev_bound hq A hA hAnorm) n

theorem norm_companion_pow_le {q : ℝ} (hq : 0 < q)
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (n : ℕ) :
    ‖companion q A ^ n‖ ≤
      (‖normalizedCompanion q A‖ + 1) * ((n : ℝ) + 1) * q ^ n := by
  exact norm_companion_pow_le_of_chebyshev_bound hq A
    (normalizedVertex_chebyshev_bound hq A hA hAnorm) n

theorem exists_norm_edgeOperator_pow_bound {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[ℂ] V) (J : V ≃ₗᵢ[ℂ] V) (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖edgeOperator (1 + q ^ 2) (q ^ 2)
        F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
          K * ((n : ℝ) + 1) * q ^ n := by
  exact exists_norm_edgeOperator_pow_bound_of_chebyshev_bound hq hq1 F H J A hAnorm
    (normalizedVertex_chebyshev_bound hq A hA hAnorm) hFH hJF hJH

theorem summable_norm_edgeOperator_pow {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[ℂ] V) (J : V ≃ₗᵢ[ℂ] V) (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    Summable (fun n : ℕ => ‖edgeOperator (1 + q ^ 2) (q ^ 2)
      F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖) := by
  exact summable_norm_edgeOperator_pow_of_chebyshev_bound hq hq1 F H J A hAnorm
    (normalizedVertex_chebyshev_bound hq A hA hAnorm) hFH hJF hJH

end Complex

section Real
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem normalizedVertex_chebyshev_bound_real {q : ℝ} (hq : 0 < q)
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (n : ℕ) : ‖Polynomial.aeval (normalizedVertex q A)
      (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1 := by
  exact norm_aeval_chebyshev_U_le_real (normalizedVertex q A)
    (normalizedVertex_selfAdjoint q A hA) (norm_normalizedVertex_le_one hq A hAnorm) n

theorem exists_norm_edgeOperator_pow_bound_real {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[ℝ] V) (J : V ≃ₗᵢ[ℝ] V) (A : E →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖edgeOperator (1 + q ^ 2) (q ^ 2)
        F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
          K * ((n : ℝ) + 1) * q ^ n := by
  exact exists_norm_edgeOperator_pow_bound_of_chebyshev_bound hq hq1 F H J A hAnorm
    (normalizedVertex_chebyshev_bound_real hq A hA hAnorm) hFH hJF hJH

theorem summable_norm_edgeOperator_pow_real {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (F H : E →ₗᵢ[ℝ] V) (J : V ≃ₗᵢ[ℝ] V) (A : E →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hAnorm : ‖A‖ ≤ vertexRate q)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) :
    Summable (fun n : ℕ => ‖edgeOperator (1 + q ^ 2) (q ^ 2)
      F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖) := by
  exact summable_norm_edgeOperator_pow_of_chebyshev_bound hq hq1 F H J A hAnorm
    (normalizedVertex_chebyshev_bound_real hq A hA hAnorm) hFH hJF hJH

end Real

end Problem367.NonbacktrackingComplement

end

end OAI
