import OAI.Analysis.KadisonKastler.ScalarRecovery

namespace OAI

/-! # Turning scalar spectral tails into compressed recovery estimates -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

local instance spectralRecoveryOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance spectralRecoveryStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- The degree-two consequence of freeness used for the tail estimate. -/
def ProjectionTraceIndependent (τ : FaithfulTracialState B) (p : B)
    (A : StarSubalgebra ℂ B) : Prop :=
  ∀ a ∈ A, τ.toLinearMap (p * a) = τ.toLinearMap p * τ.toLinearMap a

private theorem traceTwoNorm_projection_left_sq (τ : FaithfulTracialState B)
    (p x : B) (hp : IsStarProjection p) :
    traceTwoNorm τ (p * x) ^ 2 = (τ.toLinearMap (p * (x * star x))).re := by
  rw [traceTwoNorm_sq]
  congr 1
  calc
    τ.toLinearMap (star (p * x) * (p * x)) =
        τ.toLinearMap (star x * (p * p) * x) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      congr 1
      noncomm_ring
    _ = τ.toLinearMap (star x * (p * x)) := by rw [hp.isIdempotentElem.eq, mul_assoc]
    _ = τ.toLinearMap ((p * x) * star x) := τ.tracial _ _
    _ = τ.toLinearMap (p * (x * star x)) := by rw [mul_assoc]

private theorem traceTwoNorm_projection_right_sq (τ : FaithfulTracialState B)
    (p x : B) (hp : IsStarProjection p) :
    traceTwoNorm τ (x * p) ^ 2 = (τ.toLinearMap (p * (star x * x))).re := by
  rw [traceTwoNorm_sq]
  congr 1
  calc
    τ.toLinearMap (star (x * p) * (x * p)) =
        τ.toLinearMap (p * (star x * x) * p) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      congr 1
      noncomm_ring
    _ = τ.toLinearMap (p * (p * (star x * x))) := τ.tracial _ _
    _ = τ.toLinearMap (p * (star x * x)) := by
      rw [← mul_assoc, hp.isIdempotentElem.eq]

/-- The left and right factors in the tail Hölder estimate have the
same squared two-norm, equal to the scalar tail divided by the matrix size. -/
theorem spectral_tail_factor_norms (τ : FaithfulTracialState B)
    {A : StarSubalgebra ℂ B} {p f e : B} {n : ℕ}
    (hp : IsStarProjection p) (he : IsStarProjection e)
    (hf : f ∈ A) (heA : e ∈ A) (hfe : Commute f e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (hind : ProjectionTraceIndependent τ p A) :
    traceTwoNorm τ (p * f * (1 - e)) ^ 2 =
        (n : ℝ)⁻¹ * (τ.toLinearMap (star f * f * (1 - e))).re ∧
    traceTwoNorm τ ((1 - e) * f * p) ^ 2 =
        (n : ℝ)⁻¹ * (τ.toLinearMap (star f * f * (1 - e))).re := by
  let q := 1 - e
  have hq : IsStarProjection q := he.one_sub
  have hqA : q ∈ A := A.sub_mem A.one_mem heA
  have hfq : Commute f q := (Commute.one_right f).sub_right hfe
  have htraceL : τ.toLinearMap ((f * q) * star (f * q)) =
      τ.toLinearMap (star f * f * q) := by
    rw [star_mul, hq.isSelfAdjoint.star_eq]
    calc
      τ.toLinearMap (f * q * (q * star f)) =
          τ.toLinearMap (f * (q * q) * star f) := by congr 1; noncomm_ring
      _ = τ.toLinearMap (f * q * star f) := by rw [hq.isIdempotentElem.eq]
      _ = τ.toLinearMap (star f * (f * q)) := τ.tracial _ _
      _ = _ := by rw [← mul_assoc]
  have htraceR : τ.toLinearMap (star (q * f) * (q * f)) =
      τ.toLinearMap (star f * f * q) := by
    rw [star_mul, hq.isSelfAdjoint.star_eq]
    congr 1
    calc
      star f * q * (q * f) = star f * (q * q) * f := by noncomm_ring
      _ = star f * (q * f) := by rw [hq.isIdempotentElem.eq, mul_assoc]
      _ = star f * f * q := by rw [← hfq.eq, ← mul_assoc]
  constructor
  · rw [mul_assoc, traceTwoNorm_projection_left_sq τ p (f * q) hp,
      hind _ (A.mul_mem (A.mul_mem hf hqA) (A.star_mem' (A.mul_mem hf hqA))),
      hpτ, htraceL]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  · rw [traceTwoNorm_projection_right_sq τ p (q * f) hp,
      hind _ (A.mul_mem (A.star_mem' (A.mul_mem hqA hf)) (A.mul_mem hqA hf)),
      hpτ, htraceR]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl

/-- Freeness removes the factor `n` from the one-norm tail of the
compressed square. Only the scalar Haar tail remains. -/
theorem compressed_spectral_tail_le (τ : FaithfulTracialState B)
    {A : StarSubalgebra ℂ B} {p f e : B} {n : ℕ} (hn : 0 < n)
    (hp : IsStarProjection p) (he : IsStarProjection e)
    (hf : f ∈ A) (heA : e ∈ A) (hfe : Commute f e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (hind : ProjectionTraceIndependent τ p A) :
    (n : ℝ) * traceOneNorm τ
      (recoveryCompression p f - p * e * (f * f) * e * p) ≤
        (τ.toLinearMap (star f * f * (1 - e))).re := by
  obtain ⟨hL, hR⟩ := spectral_tail_factor_norms τ hp he hf heA hfe hpτ hind
  have heq : traceTwoNorm τ (p * f * (1 - e)) =
      traceTwoNorm τ ((1 - e) * f * p) := by
    nlinarith [traceTwoNorm_nonneg τ (p * f * (1 - e)),
      traceTwoNorm_nonneg τ ((1 - e) * f * p)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : (n : ℝ) *
      (traceTwoNorm τ (p * f * (1 - e)) * traceTwoNorm τ ((1 - e) * f * p)) =
        (τ.toLinearMap (star f * f * (1 - e))).re := by
    rw [← heq, ← pow_two, hL, ← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul]
  exact (mul_le_mul_of_nonneg_left
    (compression_square_tail_one_le τ p f e he hfe) hnR.le).trans_eq hmul

/-- For a normal polynomial the absolute value of its compressed square
is precisely the compressed energy. -/
theorem normal_compressed_square_mass (τ : FaithfulTracialState B)
    {f e : B} (hf : IsStarNormal f) (he : IsStarProjection e) (hfe : Commute f e) :
    traceOneNorm τ (e * (f * f) * e) = (τ.toLinearMap (star f * f * e)).re := by
  have hef : Commute e (f * f) := hfe.symm.mul_right hfe.symm
  have hestar : Commute e (star (f * f)) := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq] using hef.star_star
  have heq : e * (f * f) * e = e * (f * f) := by
    calc
      e * (f * f) * e = e * ((f * f) * e) := mul_assoc _ _ _
      _ = e * (e * (f * f)) := by rw [← hef.eq]
      _ = e * (f * f) := by rw [← mul_assoc, he.isIdempotentElem.eq]
  rw [traceOneNorm, heq, hef.cfcAbs_mul_eq hestar, CFC.abs_of_nonneg e he.nonneg,
    CFC.abs_mul_self f hf, τ.tracial]

/-- Unit total energy and a scalar tail bound give the mass hypothesis
in scalar recovery, without another analytic estimate. -/
theorem normal_compressed_square_mass_lower (τ : FaithfulTracialState B)
    {f e : B} {tail : ℝ} (hf : IsStarNormal f) (he : IsStarProjection e)
    (hfe : Commute f e) (hunit : τ.toLinearMap (star f * f) = 1)
    (htail : (τ.toLinearMap (star f * f * (1 - e))).re ≤ tail) :
    1 - tail ≤ traceOneNorm τ (e * (f * f) * e) := by
  rw [normal_compressed_square_mass τ hf he hfe]
  rw [mul_sub, mul_one, map_sub, hunit, Complex.sub_re, Complex.one_re] at htail
  linarith

end

end KadisonKastler

end OAI
