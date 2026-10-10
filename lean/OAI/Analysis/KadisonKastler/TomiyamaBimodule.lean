import OAI.Analysis.KadisonKastler.TomiyamaProjection

namespace OAI

/-! # Bimodule identities for projections

The opposite-corner norm comparison completes the algebraic part of
Tomiyama's theorem. The last theorem extends the identities whenever the
target is the norm closure of the span of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hP hfix

private theorem tomiyama_no_reverse_block (e : B) (he : IsStarProjection e)
    (z : A) (hel : φ e * z = z) (her : z * φ e = 0) :
    (1 - e) * P z * e = 0 := by
  let w := (1 - e) * P z * e
  have hew : e * w = 0 := by
    dsimp [w]
    rw [← mul_assoc, ← mul_assoc, he.mul_one_sub_self, zero_mul, zero_mul]
  have hwe : w * e = w := by
    dsimp [w]
    rw [mul_assoc, he.isIdempotentElem.eq]
  by_contra hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let t : ℝ := (‖z‖ + 1) / ‖w‖
  have ht : 0 ≤ t := div_nonneg (by positivity) hwn.le
  have htw : t * ‖w‖ = ‖z‖ + 1 := div_mul_cancel₀ _ hwn.ne'
  have hnorm : ‖z + t • φ w‖ ≤ ‖z‖ + 1 := by
    rw [norm_add_eq_max_opposite_corners (φ e) z (t • φ w)
      (he.map φ).isSelfAdjoint hel her]
    · apply max_le
      · linarith
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        exact (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ w) ht).trans htw.le
    · rw [mul_smul_comm, ← map_mul, hew, map_zero, smul_zero]
    · rw [smul_mul_assoc, ← map_mul, hwe]
  have hcomp : (1 - e) * (P z + t • w) * e = (1 + t) • w := by
    have hqw : (1 - e) * w = w := by
      dsimp [w]
      rw [← mul_assoc, ← mul_assoc, he.one_sub.isIdempotentElem.eq]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hqw, hwe]
    change w + t • w = (1 + t) • w
    module
  have hlow : (1 + t) * ‖w‖ ≤ ‖z‖ + 1 := by
    calc
      (1 + t) * ‖w‖ = ‖(1 + t) • w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + t)]
      _ = ‖(1 - e) * (P z + t • w) * e‖ := congrArg norm hcomp.symm
      _ ≤ ‖P z + t • w‖ := norm_two_projection_compression_le _ _ _ he.one_sub he
      _ = ‖P (z + t • φ w)‖ := by rw [map_add, P.map_smul_of_tower, hfix]
      _ ≤ ‖z + t • φ w‖ := hP _
      _ ≤ ‖z‖ + 1 := hnorm
  nlinarith

/-- Retractions preserve the orientation of off-diagonal blocks. -/
theorem tomiyama_offDiagonal (e : B) (he : IsStarProjection e)
    (z : A) (hel : φ e * z = z) (her : z * φ e = 0) :
    P z = e * P z * (1 - e) := by
  have hd₁ := tomiyama_compressed_zero_of_mul_right_zero φ P hP hfix e he z her
  have hqz : φ (1 - e) * z = 0 := by
    rw [map_sub, map_one, sub_mul, one_mul, hel, sub_self]
  have hd₂ := tomiyama_compressed_zero_of_mul_left_zero φ P hP hfix
    (1 - e) he.one_sub z hqz
  have hr := tomiyama_no_reverse_block φ P hP hfix e he z hel her
  have hsplit : P z = e * P z * e + e * P z * (1 - e) +
      (1 - e) * P z * e + (1 - e) * P z * (1 - e) := by noncomm_ring
  simpa only [hd₁, hd₂, hr, zero_add, add_zero] using hsplit

/-- Left multiplication by any projection in the target commutes with the
contractive retraction. -/
theorem tomiyama_map_projection_mul (e : B) (he : IsStarProjection e) (x : A) :
    P (φ e * x) = e * P x := by
  let q := 1 - e
  have hφ : φ e * φ e = φ e := by rw [← map_mul, he.isIdempotentElem.eq]
  have hq : IsStarProjection q := he.one_sub
  have hφq : φ q * φ q = φ q := by rw [← map_mul, hq.isIdempotentElem.eq]
  have heq : φ e * φ q = 0 := by rw [← map_mul, he.mul_one_sub_self, map_zero]
  have hqe : φ q * φ e = 0 := by rw [← map_mul, he.one_sub_mul_self, map_zero]
  let a := P (φ e * x * φ e)
  let b := P (φ e * x * φ q)
  let c := P (φ q * x * φ e)
  let d := P (φ q * x * φ q)
  have ha : e * a = a := by
    have hs := tomiyama_corner_supported φ P hP hfix e he x
    dsimp [a]
    calc
      e * P (φ e * x * φ e) = e * (e * P (φ e * x * φ e) * e) := congrArg (e * ·) hs.symm
      _ = P (φ e * x * φ e) := by rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq, hs]
  have hb : e * b = b := by
    have hs := tomiyama_offDiagonal φ P hP hfix e he (φ e * x * φ q)
      (by rw [← mul_assoc, ← mul_assoc, hφ])
      (by rw [mul_assoc, hqe, mul_zero])
    dsimp [b]
    calc
      e * P (φ e * x * φ q) = e * (e * P (φ e * x * φ q) * q) := congrArg (e * ·) hs
      _ = P (φ e * x * φ q) := by
        rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq]
        exact hs.symm
  have hc : e * c = 0 := by
    have hs := tomiyama_offDiagonal φ P hP hfix q hq (φ q * x * φ e)
      (by rw [← mul_assoc, ← mul_assoc, hφq])
      (by rw [mul_assoc, heq, mul_zero])
    dsimp [c]
    rw [hs]
    change e * (q * P (φ q * x * φ e) * (1 - q)) = 0
    rw [← mul_assoc, ← mul_assoc]
    have heq' : e * q = 0 := he.mul_one_sub_self
    rw [heq', zero_mul, zero_mul]
  have hd : e * d = 0 := by
    have hs := tomiyama_corner_supported φ P hP hfix q hq x
    dsimp [d]
    rw [← hs, ← mul_assoc, ← mul_assoc]
    have heq' : e * q = 0 := he.mul_one_sub_self
    rw [heq', zero_mul, zero_mul]
  have hsplit : x = φ e * x * φ e + φ e * x * φ q +
      φ q * x * φ e + φ q * x * φ q := by
    dsimp [q]
    rw [map_sub, map_one]
    noncomm_ring
  have hPx : P x = a + b + c + d := by rw [hsplit, map_add, map_add, map_add]
  have hleft : φ e * x = φ e * x * φ e + φ e * x * φ q := by
    dsimp [q]
    rw [map_sub, map_one]
    noncomm_ring
  rw [hleft, map_add, hPx, mul_add, mul_add, mul_add, ha, hb, hc, hd, add_zero, add_zero]

/-- The right identity follows by taking adjoints. -/
theorem tomiyama_map_mul_projection (e : B) (he : IsStarProjection e) (x : A) :
    P (x * φ e) = P x * e := by
  have hstar := unital_contraction_map_star P hP
    (by simpa only [map_one] using hfix 1)
  have h := congrArg star (tomiyama_map_projection_mul φ P hP hfix e he (star x))
  simpa only [← hstar, star_mul, star_star, he.isSelfAdjoint.star_eq,
    (he.map φ).isSelfAdjoint.star_eq] using h

end

end KadisonKastler

end OAI
