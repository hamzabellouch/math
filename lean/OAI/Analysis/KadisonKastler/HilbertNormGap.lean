import OAI.Analysis.KadisonKastler.RepresentationRowVariance

namespace OAI

/-! Scalar Hilbert-space norm estimates for the spectral-cut step in
Paulsen's averaging proof (JFA157 (1998), proof of Theorem5.8, pp379–380).
-/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem opNorm_sq_le_of_pointwise_sq_le (T : H →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ ξ, ‖T ξ‖ ^ 2 ≤ c * ‖ξ‖ ^ 2) : ‖T‖ ^ 2 ≤ c := by
  have hb : ‖T‖ ≤ Real.sqrt c := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg c)
    intro ξ
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg ξ))).mp
    rw [mul_pow, Real.sq_sqrt hc]
    exact hT ξ
  nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c, norm_nonneg T]

theorem not_uniform_positive_norm_gap [Nontrivial H] (T : H →L[ℂ] K)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ ξ, ‖T ξ‖ ^ 2 + δ * ‖ξ‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖ξ‖ ^ 2) : False := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨ξ, hξ⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  have hpoint := hgap ξ
  rw [hξ, one_pow, mul_one, mul_one] at hpoint
  have hc : 0 ≤ ‖T‖ ^ 2 - δ := by nlinarith [sq_nonneg ‖T ξ‖]
  have hn := opNorm_sq_le_of_pointwise_sq_le T hc (fun η => by
    have h := hgap η
    nlinarith)
  linarith

theorem projection_complement_norm_sq [CompleteSpace K]
    (P : K →L[ℂ] K) (hP : IsStarProjection P) (v : K) :
    ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hi : P (P v) = P v := congrArg (fun T : K →L[ℂ] K => T v) hP.isIdempotentElem.eq
  have ho : inner ℂ (P v) (v - P v) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hs, map_sub, hi, sub_self, inner_zero_right]
  have he : P v + (v - P v) = v := by abel
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P v) (v - P v) ho
  rw [he] at hn
  simpa only [pow_two] using hn.symm

theorem norm_preserving_projection_no_coercive_complement
    [Nontrivial H] [CompleteSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : H →L[ℂ] K) (P : K →L[ℂ] K) (hP : IsStarProjection P)
    (A : K →L[ℂ] E) (hnorm : ‖P.comp T‖ = ‖T‖)
    {t : ℝ} (ht : 0 < t)
    (hlower : ∀ ξ, t * ‖ξ‖ ^ 2 ≤ ‖A (T ξ - P (T ξ))‖ ^ 2) : False := by
  let d : ℝ := max 1 ‖A‖
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hAd : ‖A‖ ≤ d := le_max_right _ _
  have hg : 0 < t / d ^ 2 := div_pos ht hd2
  apply not_uniform_positive_norm_gap (P.comp T) hg
  intro ξ
  have hb : ‖A (T ξ - P (T ξ))‖ ^ 2 ≤ d ^ 2 * ‖T ξ - P (T ξ)‖ ^ 2 := by
    have hn := (A.le_opNorm (T ξ - P (T ξ))).trans
      (mul_le_mul_of_nonneg_right hAd (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hsmall : (t / d ^ 2) * ‖ξ‖ ^ 2 ≤ ‖T ξ - P (T ξ)‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hd2).mpr ((hlower ξ).trans (by simpa only [mul_comm] using hb))
  have hp := projection_complement_norm_sq P hP (T ξ)
  have hT : ‖T ξ‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖ξ‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm ξ) 2
  change ‖P (T ξ)‖ ^ 2 + _ ≤ _
  rw [hnorm]
  linarith

end

end KadisonKastler

end OAI
