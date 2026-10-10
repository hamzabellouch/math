import OAI.Analysis.OInfinity.CornerContractionPath

namespace OAI

/-! # The three homogeneous components of the cancellation path

The explicit two-corner cancellation has a diagonal part and two
opposite off-diagonal parts. For corners of degrees differing by one,
these have total degrees 0, -1 and 1. This finite formula is the input
needed before transporting a fragmentation path through cyclic towers.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma compression_mul_isometry (a u : E) (ha : star a * a = 1) :
    cornerCompression a u * a = a * u := by
  have haa : (a * star a) * a = a := by rw [mul_assoc, ha, mul_one]
  unfold cornerCompression
  rw [add_mul, sub_mul, one_mul, haa]
  have hau : (a * u * star a) * a = a * u := by rw [mul_assoc, ha, mul_one]
  rw [hau]
  abel

private lemma compression_mul_orthogonal (a b u : E) (hab : star a * b = 0) :
    cornerCompression a u * b = b := by
  unfold cornerCompression
  simp only [add_mul, sub_mul, one_mul, mul_assoc, hab, mul_zero, zero_add, sub_zero]

/-- The second range rotates into the first with the stated sign. -/
lemma cornerRotation_mul_second (a b : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (θ : ℝ) :
    partialIsometryBergRotation (b * star a) θ * b =
      (Real.cos θ) • b - (Real.sin θ) • a := by
  obtain ⟨_, _, hi, hf⟩ := cornerRotation_relations 1 a b ha hb hab (mul_one _) (mul_one _)
  have h₁ : (a * star a) * b = 0 := by rw [mul_assoc, hab, mul_zero]
  have h₂ : (b * star b) * b = b := by rw [mul_assoc, hb, mul_one]
  have h₃ : (b * star a) * b = 0 := by rw [mul_assoc, hab, mul_zero]
  have h₄ : (a * star b) * b = a := by rw [mul_assoc, hb, mul_one]
  unfold partialIsometryBergRotation bergRotationCore bergSupport bergSkew
  rw [hi, hf]
  simp only [star_mul, star_star, add_mul, sub_mul, smul_mul_assoc,
    one_mul, h₁, h₂, h₃, h₄, zero_add, sub_self, zero_sub, smul_neg]
  module

private lemma compression_two_vector_formula (a b u : E) (c s : ℝ)
    (ha : star a * a = 1) (hab : star a * b = 0)
    (hu : u * star u = 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    cornerCompression a u * cornerCompression (c • b - s • a) (star u) =
      1 + (c ^ 2) • (a * (u - 1) * star a + b * (star u - 1) * star b) +
        (s * c) • (a * (u - 1) * star b - b * (star u - 1) * star a) := by
  let v := c • b - s • a
  have hav : cornerCompression a u * v = c • b - s • (a * u) := by
    dsimp only [v]
    rw [mul_sub, mul_smul_comm, mul_smul_comm,
      compression_mul_orthogonal a b u hab, compression_mul_isometry a u ha]
  have he : cornerCompression a u * cornerCompression v (star u) =
      cornerCompression a u + (cornerCompression a u * v) * (star u - 1) * star v := by
    unfold cornerCompression
    noncomm_ring
  have hus : u * (star u - 1) = -(u - 1) := by rw [mul_sub, hu, mul_one]; abel
  change cornerCompression a u * cornerCompression v (star u) = _
  rw [he, hav]
  dsimp only [v]
  have hau : a * u * (star u - 1) = -(a * (u - 1)) := by
    rw [mul_assoc, hus, mul_neg]
  simp only [star_sub, star_smul, star_trivial, sub_mul, smul_mul_assoc, hau]
  simp only [mul_sub, mul_smul_comm]
  unfold cornerCompression
  have hc : c * c = 1 - s * s := by nlinarith [hcs]
  simp only [smul_sub, smul_add, smul_smul, smul_neg, neg_mul, sub_mul, mul_one,
    pow_two, hc]
  module

/-- Exact finite-band formula for the actual cancellation path. The two
nonzero-degree coefficients are negatives of one another's adjoints. -/
lemma cornerCancellationPath_three_terms (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (hu : u * star u = 1) (θ : ℝ) :
    cornerCancellationPath a b u θ =
      1 + (Real.cos θ ^ 2) •
        (a * (u - 1) * star a + b * (star u - 1) * star b) +
      (Real.sin θ * Real.cos θ) •
        (a * (u - 1) * star b - b * (star u - 1) * star a) := by
  obtain ⟨hr, hrr, _, _⟩ := cornerRotation_relations 1 a b ha hb hab (mul_one _) (mul_one _)
  have hR := (partialIsometryBergRotation_mem (b * star a) hr hrr θ).2
  calc
    _ = cornerCompression a u *
        cornerCompression (partialIsometryBergRotation (b * star a) θ * b) (star u) := by
      unfold cornerCancellationPath
      rw [← cornerCompression_conjugate _ _ _ hR]
      noncomm_ring
    _ = cornerCompression a u *
        cornerCompression ((Real.cos θ) • b - (Real.sin θ) • a) (star u) := by
      rw [cornerRotation_mul_second a b ha hb hab]
    _ = _ := compression_two_vector_formula a b u _ _ ha hab hu (by
      nlinarith [Real.sin_sq_add_cos_sq θ])

/-- Under a phase on the first corner and no phase on the second, the
actual path has only the constant, positive and negative phase terms.
This states the phase hypotheses explicitly; it does not assume that a
cyclic tower commutes with the path. -/
lemma cornerCancellationPath_phase (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (hu : u * star u = 1)
    (φ : E →⋆ₐ[ℂ] E) (ζ : ℂ) (hζ : ζ * star ζ = 1)
    (hφa : φ a = ζ • a) (hφb : φ b = b) (hφu : φ u = u) (θ : ℝ) :
    φ (cornerCancellationPath a b u θ) =
      1 + (Real.cos θ ^ 2) •
        (a * (u - 1) * star a + b * (star u - 1) * star b) +
      (Real.sin θ * Real.cos θ) •
        (ζ • (a * (u - 1) * star b) -
          star ζ • (b * (star u - 1) * star a)) := by
  have hζ' : star ζ * ζ = 1 := by simpa only [mul_comm] using hζ
  have hr (r : ℝ) (x : E) : φ (r • x) = r • φ x :=
    φ.toAlgHom.map_smul_of_tower r x
  rw [cornerCancellationPath_three_terms a b u ha hb hab hu θ,
    map_add, map_add, map_one, hr, hr]
  simp only [map_add, map_sub, map_mul, map_star, map_one, hφa, hφb, hφu,
    star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hζ', one_smul]

end WeakPureInfiniteness

end

end OAI
