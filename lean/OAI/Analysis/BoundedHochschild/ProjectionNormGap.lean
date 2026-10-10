import OAI.Analysis.BoundedHochschild.OperatorRowAverages

namespace OAI

/-! A positive lower bound on the off-diagonal part of an operator prevents
its diagonal compression from retaining the full norm. -/

noncomputable section

open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {H K J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

lemma projection_norm_sq_split (P : K →L[ℂ] K) (hP : IsStarProjection P) (y : K) :
    ‖P y‖ ^ 2 + ‖(1 - P) y‖ ^ 2 = ‖y‖ ^ 2 := by
  have hstar : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hi : inner ℂ (P y) ((1 - P) y) = 0 := by
    have he : inner ℂ (P y) ((1 - P) y) = inner ℂ y (P ((1 - P) y)) := by
      simpa only [hstar] using ContinuousLinearMap.adjoint_inner_left P ((1 - P) y) y
    rw [he]
    have hz : P ((1 - P) y) = 0 := by
      change (P * (1 - P)) y = 0
      rw [hP.mul_one_sub_self]
      rfl
    rw [hz, inner_zero_right]
  have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P y) ((1 - P) y) hi
  have he : P y + (1 - P) y = y := by simp
  rw [he] at hh
  simpa only [sq] using hh.symm

omit [CompleteSpace H] in
lemma projection_compression_norm_of_le (P F : K →L[ℂ] K)
    (hP : IsStarProjection P) (hF : IsStarProjection F) (hFP : F.comp P = F)
    (T : H →L[ℂ] K) (hT : ‖T‖ = ‖F.comp T‖) : ‖P.comp T‖ = ‖T‖ := by
  have h₁ : ‖P.comp T‖ ≤ ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hP.norm_le P))
  have h₂ : ‖T‖ ≤ ‖P.comp T‖ := by
    rw [hT, ← hFP, ContinuousLinearMap.comp_assoc]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hF.norm_le F))
  exact le_antisymm h₁ h₂

omit [CompleteSpace H] [CompleteSpace K] in
lemma opNorm_sq_le_of_apply_sq_le (A : H →L[ℂ] K) {k : ℝ} (hk : 0 ≤ k)
    (hA : ∀ x, ‖A x‖ ^ 2 ≤ k * ‖x‖ ^ 2) : ‖A‖ ^ 2 ≤ k := by
  have hb : ‖A‖ ≤ Real.sqrt k := by
    apply A.opNorm_le_bound (Real.sqrt_nonneg k)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg k) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hk] using hA x
  nlinarith [Real.sq_sqrt hk, Real.sqrt_nonneg k, norm_nonneg A]

omit [CompleteSpace J] in
lemma no_positive_offDiagonal_gap (T : H →L[ℂ] K)
    (P : K →L[ℂ] K) (Q : H →L[ℂ] H) (C : K →L[ℂ] J)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hQ0 : Q ≠ 0)
    (hTQ : T.comp Q = T) (hnorm : ‖P.comp T‖ = ‖T‖)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x, δ * ‖Q x‖ ^ 2 ≤ ‖C ((1 - P) (T x))‖ ^ 2) : False := by
  have hbound (x : H) : δ * ‖Q x‖ ^ 2 + ‖C‖ ^ 2 * ‖P (T x)‖ ^ 2 ≤
      (‖C‖ ^ 2 * ‖T‖ ^ 2) * ‖Q x‖ ^ 2 := by
    have hg := (hgap x).trans (pow_le_pow_left₀ (norm_nonneg _)
      (C.le_opNorm ((1 - P) (T x))) 2)
    have ht : ‖T x‖ ≤ ‖T‖ * ‖Q x‖ := by
      have he := congrArg (fun A : H →L[ℂ] K => A x) hTQ
      change T (Q x) = T x at he
      rw [← he]
      exact T.le_opNorm _
    have hs := projection_norm_sq_split P hP (T x)
    have htsq := pow_le_pow_left₀ (norm_nonneg _) ht 2
    rw [mul_pow] at hg htsq
    nlinarith [mul_le_mul_of_nonneg_left htsq (sq_nonneg ‖C‖)]
  let k := ‖C‖ ^ 2 * ‖T‖ ^ 2 - δ
  have hk : 0 ≤ k := by
    obtain ⟨x, hx⟩ : ∃ x : H, Q x ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ0 (ContinuousLinearMap.ext h)
    have hh := hbound x
    have hxpos : 0 < ‖Q x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    dsimp [k]
    nlinarith [mul_nonneg (sq_nonneg ‖C‖) (sq_nonneg ‖P (T x)‖)]
  have hs (x : H) : ‖(‖C‖ • P.comp T) x‖ ^ 2 ≤ k * ‖x‖ ^ 2 := by
    have hh := hbound x
    have hqx : ‖Q x‖ ≤ ‖x‖ :=
      (Q.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) (hQ.norm_le Q))
    have hqsq := pow_le_pow_left₀ (norm_nonneg _) hqx 2
    have hkm := mul_le_mul_of_nonneg_left hqsq hk
    simp only [smul_apply, ContinuousLinearMap.comp_apply, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg C), mul_pow]
    dsimp [k] at hkm ⊢
    nlinarith
  have hh := opNorm_sq_le_of_apply_sq_le (‖C‖ • P.comp T) hk hs
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg C), mul_pow, hnorm] at hh
  dsimp [k] at hh
  linarith

end BoundedHochschild.KadisonRingrose

end

end OAI
