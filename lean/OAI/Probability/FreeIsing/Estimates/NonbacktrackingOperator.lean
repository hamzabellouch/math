import OAI.Probability.FreeIsing.Spectral.ChebyshevRecurrence

namespace OAI

namespace Problem367

theorem summable_norm_of_affine_geometric_bound {F : Type*} [SeminormedAddCommGroup F]
    (f : ℕ → F) (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ C * ((n : ℝ) + 1) * q ^ n) :
    Summable (fun n : ℕ => ‖f n‖) := by
  have hqnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    simpa only [pow_one, add_mul, one_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm).add
        (summable_geometric_of_norm_lt_one hqnorm)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  simpa only [mul_assoc] using hs.mul_left C

section RCLikeOperators
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

def diagonalOperator (B : E →L[𝕜] E) : E × E →L[𝕜] E × E := B.prodMap B

def nonbacktrackingOperator (B c d : E →L[𝕜] E) : E × E →L[𝕜] E × E :=
  (-(c.comp (ContinuousLinearMap.snd 𝕜 E E))).prod
    (d.comp (ContinuousLinearMap.fst 𝕜 E E) + (2 * B).comp (ContinuousLinearMap.snd 𝕜 E E))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
@[simp]
theorem diagonalOperator_apply (B : E →L[𝕜] E) (x : E × E) :
    diagonalOperator B x = (B x.1, B x.2) := rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
@[simp]
theorem nonbacktrackingOperator_apply (B c d : E →L[𝕜] E) (x : E × E) :
    nonbacktrackingOperator B c d x = (-c x.2, d x.1 + B x.2 + B x.2) := by
  simp [nonbacktrackingOperator, two_mul, add_assoc]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in

theorem nonbacktrackingOperator_quadratic {B c d : E →L[𝕜] E}
    (hcd : c * d = 1) (hdc : d * c = 1) (hcB : Commute c B) :
    nonbacktrackingOperator B c d ^ 2 =
      2 * diagonalOperator B * nonbacktrackingOperator B c d - 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have hcdx : c (d x.1) = x.1 := by
    have hh := congrArg (fun T : E →L[𝕜] E => T x.1) hcd
    simpa using hh
  have hdcx : d (c x.2) = x.2 := by
    have hh := congrArg (fun T : E →L[𝕜] E => T x.2) hdc
    simpa using hh
  have hcBx : c (B x.2) = B (c x.2) := by
    have hh := congrArg (fun T : E →L[𝕜] E => T x.2) hcB.eq
    simpa using hh
  apply Prod.ext <;>
    simp [pow_two, two_mul, nonbacktrackingOperator_apply, diagonalOperator_apply,
      hcdx, hdcx, hcBx] <;> abel

def diagonalOperatorAlgHom : (E →L[𝕜] E) →ₐ[ℝ] (E × E →L[𝕜] E × E) where
  toFun := diagonalOperator
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_mul' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    rfl
  commutes' := by
    intro r
    apply ContinuousLinearMap.ext
    intro x
    rfl

theorem aeval_diagonalOperator (B : E →L[𝕜] E) (p : Polynomial ℝ) :
    Polynomial.aeval (diagonalOperator B) p = diagonalOperator (Polynomial.aeval B p) :=
  Polynomial.aeval_algHom_apply diagonalOperatorAlgHom B p

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in

theorem norm_diagonalOperator_le (B : E →L[𝕜] E) : ‖diagonalOperator B‖ ≤ ‖B‖ := by
  apply (diagonalOperator B).opNorm_le_bound (norm_nonneg B)
  intro x
  change max ‖B x.1‖ ‖B x.2‖ ≤ ‖B‖ * max ‖x.1‖ ‖x.2‖
  apply max_le
  · exact (B.le_opNorm x.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg B))
  · exact (B.le_opNorm x.2).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg B))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in

theorem norm_nonbacktrackingOperator_le (B c d : E →L[𝕜] E) :
    ‖nonbacktrackingOperator B c d‖ ≤ max ‖c‖ (‖d‖ + 2 * ‖B‖) := by
  have hfst (T : E →L[𝕜] E) : ‖T.comp (ContinuousLinearMap.fst 𝕜 E E)‖ ≤ ‖T‖ := by
    calc
      ‖T.comp (ContinuousLinearMap.fst 𝕜 E E)‖ ≤
          ‖T‖ * ‖ContinuousLinearMap.fst 𝕜 E E‖ := T.opNorm_comp_le _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_fst_le 𝕜 E E) (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  have hsnd (T : E →L[𝕜] E) : ‖T.comp (ContinuousLinearMap.snd 𝕜 E E)‖ ≤ ‖T‖ := by
    calc
      ‖T.comp (ContinuousLinearMap.snd 𝕜 E E)‖ ≤
          ‖T‖ * ‖ContinuousLinearMap.snd 𝕜 E E‖ := T.opNorm_comp_le _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_snd_le 𝕜 E E) (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  have htwo : ‖(2 : E →L[𝕜] E) * B‖ ≤ 2 * ‖B‖ := by
    simpa only [two_mul] using norm_add_le B B
  rw [nonbacktrackingOperator, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_neg]
  apply max_le_max (hsnd c)
  exact (norm_add_le _ _).trans (add_le_add (hfst d) ((hsnd (2 * B)).trans htwo))

theorem norm_nonbacktrackingOperator_pow_le {B c d : E →L[𝕜] E}
    (hcd : c * d = 1) (hdc : d * c = 1) (hcB : Commute c B)
    (hU : ∀ n : ℕ,
      ‖Polynomial.aeval B (Polynomial.Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1)
    (n : ℕ) :
    ‖nonbacktrackingOperator B c d ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * ‖nonbacktrackingOperator B c d‖ + n := by
  let : NormedAlgebra ℝ (E × E →L[𝕜] E × E) :=
    { (inferInstance : Algebra ℝ (E × E →L[𝕜] E × E)),
      (inferInstance : NormedSpace ℝ (E × E →L[𝕜] E × E)) with }
  apply norm_pow_le_of_chebyshev_bound (nonbacktrackingOperator_quadratic hcd hdc hcB)
  intro k
  rw [aeval_diagonalOperator]
  exact (norm_diagonalOperator_le _).trans (hU k)

end RCLikeOperators

section ComplexHilbertOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_nonbacktrackingOperator_pow_le_of_selfAdjoint {B c d : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1)
    (hcd : c * d = 1) (hdc : d * c = 1) (hcB : Commute c B) (n : ℕ) :
    ‖nonbacktrackingOperator B c d ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * ‖nonbacktrackingOperator B c d‖ + n := by
  nontriviality E
  exact norm_nonbacktrackingOperator_pow_le hcd hdc hcB
    (fun k => norm_aeval_chebyshev_U_le k hB hBnorm) n

theorem norm_nonbacktrackingOperator_scalar_pow_le {B : E →L[ℂ] E} {q : ℝ}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (hq : q ≠ 0) (n : ℕ) :
    ‖nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
      (algebraMap ℝ (E →L[ℂ] E) q⁻¹) ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * ‖nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
        (algebraMap ℝ (E →L[ℂ] E) q⁻¹)‖ + n := by
  apply norm_nonbacktrackingOperator_pow_le_of_selfAdjoint hB hBnorm
  · rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  · rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  · exact Algebra.commutes q B

theorem norm_nonbacktrackingOperator_scalar_le {B : E →L[ℂ] E} (q : ℝ)
    (hBnorm : ‖B‖ ≤ 1) :
    ‖nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
      (algebraMap ℝ (E →L[ℂ] E) q⁻¹)‖ ≤ |q| + |q⁻¹| + 2 := by
  have hh := norm_nonbacktrackingOperator_le B
    (algebraMap ℝ (E →L[ℂ] E) q) (algebraMap ℝ (E →L[ℂ] E) q⁻¹)
  simp only [norm_algebraMap, Real.norm_eq_abs] at hh
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hq : |q| * ‖(1 : E →L[ℂ] E)‖ ≤ |q| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (abs_nonneg q)
  have hqi : |q⁻¹| * ‖(1 : E →L[ℂ] E)‖ ≤ |q⁻¹| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (abs_nonneg q⁻¹)
  apply hh.trans
  apply max_le <;> nlinarith [abs_nonneg q, abs_nonneg q⁻¹]

theorem norm_scaled_nonbacktrackingOperator_pow_le {B : E →L[ℂ] E} {q : ℝ}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (hq : 0 < q) (n : ℕ) :
    ‖((q : ℂ) • nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
      (algebraMap ℝ (E →L[ℂ] E) q⁻¹)) ^ n‖ ≤
      (q + q⁻¹ + 3) * ((n : ℝ) + 1) * q ^ n := by
  let Z := nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
    (algebraMap ℝ (E →L[ℂ] E) q⁻¹)
  have hZ : ‖Z‖ ≤ q + q⁻¹ + 2 := by
    simpa only [Z, abs_of_pos hq, abs_of_pos (inv_pos.mpr hq)] using
      norm_nonbacktrackingOperator_scalar_le q hBnorm
  have hp : ∀ k : ℕ, ‖Z ^ k‖ ≤ (q + q⁻¹ + 3) * ((k : ℝ) + 1) := by
    intro k
    cases k with
    | zero =>
      have hone : ‖(1 : E × E →L[ℂ] E × E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      simp only [pow_zero, Nat.cast_zero, zero_add, mul_one]
      exact hone.trans (by linarith [inv_pos.mpr hq])
    | succ k =>
      have hh := norm_nonbacktrackingOperator_scalar_pow_le hB hBnorm hq.ne' k
      change ‖Z ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * ‖Z‖ + k at hh
      have hmul := mul_le_mul_of_nonneg_left hZ (by positivity : 0 ≤ (k : ℝ) + 1)
      simp only [Nat.cast_succ]
      nlinarith [inv_pos.mpr hq]
  change ‖((q : ℂ) • Z) ^ n‖ ≤ _
  rw [_root_.smul_pow]
  calc
    ‖(q : ℂ) ^ n • Z ^ n‖ ≤ q ^ n * ‖Z ^ n‖ := by
      simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using
        ContinuousLinearMap.opNorm_smul_le ((q : ℂ) ^ n) (Z ^ n)
    _ ≤ q ^ n * ((q + q⁻¹ + 3) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (hp n) (pow_nonneg hq.le n)
    _ = (q + q⁻¹ + 3) * ((n : ℝ) + 1) * q ^ n := by ring

theorem summable_norm_scaled_nonbacktrackingOperator_pow {B : E →L[ℂ] E} {q : ℝ}
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    Summable (fun n : ℕ =>
      ‖((q : ℂ) • nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
        (algebraMap ℝ (E →L[ℂ] E) q⁻¹)) ^ n‖) := by
  exact summable_norm_of_affine_geometric_bound
    (fun n : ℕ => ((q : ℂ) • nonbacktrackingOperator B (algebraMap ℝ (E →L[ℂ] E) q)
      (algebraMap ℝ (E →L[ℂ] E) q⁻¹)) ^ n)
    (q + q⁻¹ + 3) q hq.le hq1
    (norm_scaled_nonbacktrackingOperator_pow_le hB hBnorm hq)

end ComplexHilbertOperators
end Problem367

end OAI
