import OAI.Analysis.KadisonKastler.SquareRootCompression

namespace OAI

/-! # Trace-one compression identities from explicit polar data -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

local instance traceCompressionPolarOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance traceCompressionPolarStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Positive real homogeneity of the tracial one-norm. -/
theorem traceOneNorm_smul_nonneg (τ : FaithfulTracialState B) {r : ℝ} (hr : 0 ≤ r)
    (x : B) : traceOneNorm τ (r • x) = r * traceOneNorm τ x := by
  simp only [traceOneNorm, CFC.abs_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [← Complex.coe_smul, map_smul]
  simp [smul_eq_mul, Complex.mul_re]

/-- Natural scalar homogeneity, stated with complex algebra scalars. -/
theorem traceOneNorm_nat_smul (τ : FaithfulTracialState B) (n : ℕ) (x : B) :
    traceOneNorm τ ((n : ℂ) • x) = (n : ℝ) * traceOneNorm τ x := by
  have hs : (n : ℂ) • x = (n : ℝ) • x := by simp only [Nat.cast_smul_eq_nsmul]
  rw [hs, traceOneNorm_smul_nonneg τ (Nat.cast_nonneg n)]

@[simp]
theorem traceOneNorm_neg (τ : FaithfulTracialState B) (x : B) :
    traceOneNorm τ (-x) = traceOneNorm τ x := by
  simp only [traceOneNorm, CFC.abs_neg]

/-- The algebraic polar compression identity. Only the displayed
factorization and final-projection support are used. -/
theorem traceOneNorm_selfAdjoint_polar_compression (τ : FaithfulTracialState B)
    (x b a w : B) (hb : IsSelfAdjoint b) (hx : x = b * w)
    (hw : IsStarProjection (w * star w))
    (hL : (w * star w) * b = b) (hR : b * (w * star w) = b) :
    traceOneNorm τ (star x * a * x) = traceOneNorm τ (b * a * b) := by
  have hsL : (w * star w) * (b * a * b) = b * a * b := by
    calc
      (w * star w) * (b * a * b) = ((w * star w) * b) * a * b := by noncomm_ring
      _ = b * a * b := by rw [hL]
  have hsR : (b * a * b) * (w * star w) = b * a * b := by
    calc
      (b * a * b) * (w * star w) = b * a * (b * (w * star w)) := by noncomm_ring
      _ = b * a * b := by rw [hR]
  have hi := traceOneNorm_partialIsometry_conjugate τ (star w) (b * a * b)
    (by simpa only [star_star] using hw)
    (by simpa only [star_star] using hsL) (by simpa only [star_star] using hsR)
  have he : star x * a * x = star w * (b * a * b) * star (star w) := by
    rw [hx, star_mul, hb.star_eq, star_star]
    noncomm_ring
  rw [he]
  exact hi

/-- The compression identity for the positive part of a polar factorization. -/
theorem traceOneNorm_polar_compression (τ : FaithfulTracialState B)
    (x a w : B) (hx : x = CFC.sqrt (x * star x) * w)
    (hw : IsStarProjection (w * star w))
    (hL : (w * star w) * CFC.sqrt (x * star x) = CFC.sqrt (x * star x))
    (hR : CFC.sqrt (x * star x) * (w * star w) = CFC.sqrt (x * star x)) :
    traceOneNorm τ (star x * a * x) =
      traceOneNorm τ (CFC.sqrt (x * star x) * a * CFC.sqrt (x * star x)) :=
  traceOneNorm_selfAdjoint_polar_compression τ x _ a w
    (CFC.sqrt_nonneg _).isSelfAdjoint hx hw hL hR

/-- The positive square of the scaled projection product is the
normalized compression. -/
theorem scaled_projection_product_mul_star (n : ℕ) (p e : B)
    (hp : IsStarProjection p) (he : IsStarProjection e) :
    ((Real.sqrt (n : ℝ)) • (e * p)) * star ((Real.sqrt (n : ℝ)) • (e * p)) =
      (n : ℂ) • (e * p * e) := by
  have hroot : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  simp only [star_smul, star_trivial, star_mul, hp.isSelfAdjoint.star_eq,
    he.isSelfAdjoint.star_eq, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hroot]
  have hm : (e * p) * (p * e) = e * p * e := by
    calc
      (e * p) * (p * e) = e * (p * p) * e := by noncomm_ring
      _ = e * p * e := by rw [hp.isIdempotentElem.eq]
  rw [hm]
  simp only [Nat.cast_smul_eq_nsmul]

/-- Compression by `sqrt n • ep`, in the exact form needed in scalar
recovery. The hypotheses describe the polar factor, not its existence. -/
theorem traceOneNorm_scaled_projection_compression (τ : FaithfulTracialState B)
    (n : ℕ) (p e a w : B) (hp : IsStarProjection p) (he : IsStarProjection e)
    (hx : (Real.sqrt (n : ℝ)) • (e * p) = CFC.sqrt ((n : ℂ) • (e * p * e)) * w)
    (hw : IsStarProjection (w * star w))
    (hL : (w * star w) * CFC.sqrt ((n : ℂ) • (e * p * e)) =
      CFC.sqrt ((n : ℂ) • (e * p * e)))
    (hR : CFC.sqrt ((n : ℂ) • (e * p * e)) * (w * star w) =
      CFC.sqrt ((n : ℂ) • (e * p * e))) :
    (n : ℝ) * traceOneNorm τ (p * e * a * e * p) =
      traceOneNorm τ (CFC.sqrt ((n : ℂ) • (e * p * e)) * a *
        CFC.sqrt ((n : ℂ) • (e * p * e))) := by
  let x : B := (Real.sqrt (n : ℝ)) • (e * p)
  have hi := traceOneNorm_selfAdjoint_polar_compression τ x
    (CFC.sqrt ((n : ℂ) • (e * p * e))) a w
    (CFC.sqrt_nonneg _).isSelfAdjoint hx hw hL hR
  have hroot : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hexp : star x * a * x = (n : ℂ) • (p * e * a * e * p) := by
    simp only [x, star_smul, star_trivial, star_mul, hp.isSelfAdjoint.star_eq,
      he.isSelfAdjoint.star_eq, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hroot]
    have hm : (p * e) * a * (e * p) = p * e * a * e * p := by noncomm_ring
    rw [hm]
    simp only [Nat.cast_smul_eq_nsmul]
  rwa [hexp, traceOneNorm_nat_smul] at hi

end

end KadisonKastler

end OAI
