import OAI.Analysis.KadisonKastler.BoundedSequence

namespace OAI

/-!
# Two free-projection moments for scalar recovery

Only the degree-two and alternating degree-four centered moments are
used. The identities below are proved from these explicit algebraic
hypotheses; no free-probability theorem is assumed here.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- The two centered mixed moments needed for the compressed projection. -/
structure CenteredProjectionMoments (τ : FaithfulTracialState B) (p e : B)
    (t η : ℝ) : Prop where
  two : τ.toLinearMap ((p - (t : ℂ) • 1) * (e - (η : ℂ) • 1)) = 0
  four : τ.toLinearMap ((p - (t : ℂ) • 1) * (e - (η : ℂ) • 1) *
    (p - (t : ℂ) • 1) * (e - (η : ℂ) • 1)) = 0

private theorem centered_projection_square (p : B) (hp : p * p = p) (t : ℂ) :
    (p - t • 1) * (p - t • 1) =
      (1 - 2 * t) • (p - t • 1) + (t - t ^ 2) • (1 : B) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    hp]
  module

private theorem expand_centered_sandwich (a b : B) (η : ℂ) :
    a * (b + η • 1) * a * (b + η • 1) =
      a * b * a * b + η • (a * b * a) + η • (a * a * b) + η ^ 2 • (a * a) := by
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one,
    pow_two]
  module

private theorem trace_sandwich_square (τ : FaithfulTracialState B)
    (e a : B) (he : e * e = e) :
    τ.toLinearMap ((e * a * e) * (e * a * e)) = τ.toLinearMap (a * e * a * e) := by
  calc
    τ.toLinearMap ((e * a * e) * (e * a * e)) =
        τ.toLinearMap (e * a * (e * e) * a * e) := by congr 1; noncomm_ring
    _ = τ.toLinearMap (e * a * e * a * e) := by rw [he]
    _ = τ.toLinearMap (e * (a * e * a * e)) := by congr 1; noncomm_ring
    _ = τ.toLinearMap ((a * e * a * e) * e) := τ.tracial _ _
    _ = τ.toLinearMap (a * e * a * (e * e)) := by congr 1; noncomm_ring
    _ = τ.toLinearMap (a * e * a * e) := by rw [he]

/-- The first mixed moment makes the trace of a compression the product
of the projection traces. -/
theorem CenteredProjectionMoments.trace_compression
    {τ : FaithfulTracialState B} {p e : B} {t η : ℝ}
    (h : CenteredProjectionMoments τ p e t η)
    (he : e * e = e) (hpτ : τ.toLinearMap p = (t : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ)) :
    τ.toLinearMap (e * p * e) = ((t * η : ℝ) : ℂ) := by
  have hm := h.two
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    map_sub, map_smul, τ.map_one, hpτ, heτ, smul_eq_mul] at hm
  have hpe : τ.toLinearMap (p * e) = (t : ℂ) * (η : ℂ) := by linear_combination hm
  calc
    τ.toLinearMap (e * p * e) = τ.toLinearMap (p * (e * e)) := by
      rw [mul_assoc, τ.tracial e, ← mul_assoc]
    _ = τ.toLinearMap (p * e) := by rw [he]
    _ = ((t * η : ℝ) : ℂ) := by simpa using hpe

/-- The alternating fourth moment determines the centered compressed
second moment before any normalization by the corner trace. -/
theorem CenteredProjectionMoments.trace_centered_compression
    {τ : FaithfulTracialState B} {p e : B} {t η : ℝ}
    (h : CenteredProjectionMoments τ p e t η)
    (hp : p * p = p) (hpτ : τ.toLinearMap p = (t : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ)) :
    τ.toLinearMap ((p - (t : ℂ) • 1) * e * (p - (t : ℂ) • 1) * e) =
      (η : ℂ) ^ 2 * ((t : ℂ) - (t : ℂ) ^ 2) := by
  let a : B := p - (t : ℂ) • 1
  let b : B := e - (η : ℂ) • 1
  have ha : τ.toLinearMap a = 0 := by simp [a, hpτ, τ.map_one]
  have hb : τ.toLinearMap b = 0 := by simp [b, heτ, τ.map_one]
  have hab : τ.toLinearMap (a * b) = 0 := h.two
  have habab : τ.toLinearMap (a * b * a * b) = 0 := h.four
  have hasq : a * a = (1 - 2 * (t : ℂ)) • a +
      ((t : ℂ) - (t : ℂ) ^ 2) • (1 : B) := centered_projection_square p hp t
  have haa : τ.toLinearMap (a * a) = (t : ℂ) - (t : ℂ) ^ 2 := by
    rw [hasq, map_add, map_smul, map_smul, ha, τ.map_one]
    simp
  have haab : τ.toLinearMap (a * a * b) = 0 := by
    rw [hasq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
      map_add, map_smul, map_smul, hab, hb]
    simp
  have haba : τ.toLinearMap (a * b * a) = 0 := by
    rw [τ.tracial (a * b) a, ← mul_assoc, haab]
  have he : e = b + (η : ℂ) • 1 := by simp [b]
  change τ.toLinearMap (a * e * a * e) = _
  rw [he, expand_centered_sandwich, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, habab, haba, haab, haa]
  simp

/-- The normalized positive compression has the same trace as `e`. -/
theorem CenteredProjectionMoments.trace_scaled_compression
    {τ : FaithfulTracialState B} {p e : B} {n : ℕ} {η : ℝ}
    (hn : 0 < n) (he : IsStarProjection e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ))
    (h : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ η) :
    τ.toLinearMap ((n : ℂ) • (e * p * e)) = (η : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [map_smul, h.trace_compression he.isIdempotentElem.eq hpτ heτ]
  simp only [smul_eq_mul]
  push_cast
  field_simp [hnC]

/-- With trace `1/n`, the scaled compression has the exact variance
`(n-1)η²`. This is the scalar identity used in the recovery estimate. -/
theorem CenteredProjectionMoments.trace_scaled_compression_sub_sq
    {τ : FaithfulTracialState B} {p e : B} {n : ℕ} {η : ℝ}
    (hn : 0 < n) (hp : IsStarProjection p) (he : IsStarProjection e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ))
    (h : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ η) :
    τ.toLinearMap (((n : ℂ) • (e * p * e) - e) ^ 2) =
      (((n : ℝ) - 1) * η ^ 2 : ℝ) := by
  let a : B := p - (((n : ℝ)⁻¹ : ℝ) : ℂ) • 1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnt : (n : ℂ) * (((n : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ hnC
  have hx : (n : ℂ) • (e * p * e) - e = (n : ℂ) • (e * a * e) := by
    simp only [a, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      smul_sub, smul_smul, hnt, one_smul]
    rw [mul_one, he.isIdempotentElem.eq]
  rw [hx, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, map_smul,
    trace_sandwich_square τ e a he.isIdempotentElem.eq]
  rw [h.trace_centered_compression hp.isIdempotentElem.eq hpτ heτ]
  simp only [smul_eq_mul]
  push_cast
  field_simp [hnC]

/-- The preceding complex identity is the square of the tracial
 two-norm, because the scaled compression is selfadjoint. -/
theorem CenteredProjectionMoments.traceTwoNorm_scaled_compression_sub_sq
    {τ : FaithfulTracialState B} {p e : B} {n : ℕ} {η : ℝ}
    (hn : 0 < n) (hp : IsStarProjection p) (he : IsStarProjection e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ))
    (h : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ η) :
    traceTwoNorm τ ((n : ℂ) • (e * p * e) - e) ^ 2 =
      ((n : ℝ) - 1) * η ^ 2 := by
  have hstar : star ((n : ℂ) • (e * p * e) - e) = (n : ℂ) • (e * p * e) - e := by
    simp only [star_sub, star_smul, star_mul, star_natCast,
      hp.isSelfAdjoint.star_eq, he.isSelfAdjoint.star_eq, mul_assoc]
  have hm := h.trace_scaled_compression_sub_sq hn hp he hpτ heτ
  have hnonneg : 0 ≤ ((n : ℝ) - 1) * η ^ 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    exact mul_nonneg (sub_nonneg.mpr hnR) (sq_nonneg η)
  rw [traceTwoNorm, hstar, ← pow_two, hm]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using Real.sq_sqrt hnonneg

end

end KadisonKastler

end OAI
