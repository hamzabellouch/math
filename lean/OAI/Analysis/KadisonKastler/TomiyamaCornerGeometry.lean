import OAI.Analysis.KadisonKastler.TomiyamaNormGeometry

namespace OAI

/-! # Orthogonal-corner norm calculations

These are the elementary norm estimates behind Tomiyama's projection
argument. They do not assume positivity or a representation of the algebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Compression by a star projection is contractive. -/
theorem norm_projection_compression_le (e x : A) (he : IsStarProjection e) :
    ‖e * x * e‖ ≤ ‖x‖ := by
  calc
    ‖e * x * e‖ ≤ ‖e * x‖ * ‖e‖ := norm_mul_le _ _
    _ ≤ (‖e‖ * ‖x‖) * ‖e‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖x‖) * 1 := by
      gcongr <;> exact IsStarProjection.norm_le e he
    _ = ‖x‖ := by ring

/-- Two mutually orthogonal operator blocks have the maximum norm. -/
theorem norm_add_eq_max_of_orthogonal_products (a b : A)
    (hab : star a * b = 0) (hab' : a * star b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hp : (star a * a) * (star b * b) = 0 := by
    calc
      (star a * a) * (star b * b) = star a * (a * star b) * b := by simp only [mul_assoc]
      _ = 0 := by rw [hab', mul_zero, zero_mul]
  have he : ‖a + b‖ ^ 2 = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
    calc
      ‖a + b‖ ^ 2 = ‖star (a + b) * (a + b)‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖star a * a + star b * b‖ := by
        congr 1
        simp only [star_add, add_mul, mul_add, hab, hba, add_zero, zero_add]
      _ = max ‖star a * a‖ ‖star b * b‖ :=
        (IsSelfAdjoint.star_mul_self a).norm_add_eq_max (IsSelfAdjoint.star_mul_self b) hp
      _ = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
        rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self, pow_two, pow_two]
  rcases le_total ‖a‖ ‖b‖ with h | h
  · rw [max_eq_right h]
    rw [max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h 2)] at he
    nlinarith [norm_nonneg (a + b), norm_nonneg b]
  · rw [max_eq_left h]
    rw [max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h 2)] at he
    nlinarith [norm_nonneg (a + b), norm_nonneg a]

/-- The norm estimate also holds with two different projections. -/
theorem norm_two_projection_compression_le (e f x : A)
    (he : IsStarProjection e) (hf : IsStarProjection f) :
    ‖e * x * f‖ ≤ ‖x‖ := by
  calc
    ‖e * x * f‖ ≤ ‖e * x‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ (‖e‖ * ‖x‖) * ‖f‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖x‖) * 1 := by
      gcongr
      · exact IsStarProjection.norm_le e he
      · exact IsStarProjection.norm_le f hf
    _ = ‖x‖ := by ring

/-- An upper and a lower off-diagonal block have maximum norm. -/
theorem norm_add_eq_max_opposite_corners (e a b : A) (he : IsSelfAdjoint e)
    (hea : e * a = a) (hae : a * e = 0)
    (heb : e * b = 0) (hbe : b * e = b) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have hsa : star a * e = star a := by
    simpa only [star_mul, he.star_eq] using congrArg star hea
  have hsb : e * star b = star b := by
    simpa only [star_mul, he.star_eq] using congrArg star hbe
  apply norm_add_eq_max_of_orthogonal_products
  · calc
      star a * b = (star a * e) * b := by rw [hsa]
      _ = 0 := by rw [mul_assoc, heb, mul_zero]
  · calc
      a * star b = a * (e * star b) := by rw [hsb]
      _ = 0 := by rw [← mul_assoc, hae, zero_mul]

/-- A zero product with a projection gives a quadratic perturbation bound. -/
theorem norm_projection_add_sq_le (e z : A) (he : IsStarProjection e)
    (hze : z * e = 0) (t : ℝ) :
    ‖e + t • z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2 * t ^ 2 := by
  have hes : e * star z = 0 := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq, star_zero] using congrArg star hze
  have hprod : (e + t • z) * star (e + t • z) = e + t ^ 2 • (z * star z) := by
    simp only [star_add, star_smul, star_trivial, he.isSelfAdjoint.star_eq,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hze, hes, smul_zero,
      he.isIdempotentElem.eq, add_zero, zero_add]
    module
  calc
    ‖e + t • z‖ ^ 2 = ‖(e + t • z) * star (e + t • z)‖ := by
      rw [CStarRing.norm_self_mul_star, pow_two]
    _ = ‖e + t ^ 2 • (z * star z)‖ := congrArg norm hprod
    _ ≤ ‖e‖ + ‖t ^ 2 • (z * star z)‖ := norm_add_le _ _
    _ ≤ 1 + ‖z‖ ^ 2 * t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
        CStarRing.norm_self_mul_star]
      nlinarith [IsStarProjection.norm_le e he]

/-- The left-product version follows by adjoints. -/
theorem norm_projection_add_sq_le' (e z : A) (he : IsStarProjection e)
    (hez : e * z = 0) (t : ℝ) :
    ‖e + t • z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2 * t ^ 2 := by
  have hz : star z * e = 0 := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq, star_zero] using congrArg star hez
  have h := norm_projection_add_sq_le e (star z) he hz t
  have hn : ‖e + t • star z‖ = ‖e + t • z‖ := by
    simpa only [star_add, star_smul, star_trivial, he.isSelfAdjoint.star_eq] using
      (norm_star (e + t • z))
  simpa only [hn, norm_star] using h

/-- Testing both real and imaginary perturbations forces a compressed
first-order term to vanish. -/
theorem corner_eq_zero_of_quadratic_bounds (e x : A) (he : IsStarProjection e)
    (hex : e * x = x) (hxe : x * e = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖e + t • x‖ ^ 2 ≤ 1 + C * t ^ 2)
    (hi : ∀ t : ℝ, ‖e + t • (Complex.I • x)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    x = 0 := by
  have hs := corner_skewAdjoint_of_quadratic_bound e x he hex hxe C h
  have hsi := corner_skewAdjoint_of_quadratic_bound e (Complex.I • x) he
    (by rw [mul_smul_comm, hex]) (by rw [smul_mul_assoc, hxe]) C hi
  have hself : star x = x := by
    apply smul_right_injective A (neg_ne_zero.mpr Complex.I_ne_zero)
    simpa only [star_smul, Complex.star_def, Complex.conj_I, neg_smul] using hsi
  have htwo : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc
      x + x = star x + x := congrArg (· + x) hself.symm
      _ = 0 := by rw [hs, neg_add_cancel]
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

end

end KadisonKastler

end OAI
