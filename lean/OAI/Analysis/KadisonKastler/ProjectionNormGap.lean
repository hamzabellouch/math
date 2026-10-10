import OAI.Analysis.KadisonKastler.HilbertNormGap

namespace OAI

/-! Localizing the Hilbert-space norm-gap argument to a projection range. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem projection_fixed_on_range (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (x : P.range) : P (x : H) = x := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact congrArg (fun T : H →L[ℂ] H => T y) hP.isIdempotentElem.eq

omit [CompleteSpace K] in
theorem norm_comp_projection_eq_norm_restrict
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (S : H →L[ℂ] K) :
    ‖S.comp P‖ = ‖S.comp P.range.subtypeL‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (S.comp P)
      (norm_nonneg (S.comp P.range.subtypeL))
    intro ξ
    let x : P.range := ⟨P ξ, ⟨ξ, rfl⟩⟩
    have hb := (S.comp P.range.subtypeL).le_opNorm x
    have hp : ‖P ξ‖ ≤ ‖ξ‖ := by
      simpa only [one_mul] using P.le_of_opNorm_le hP.norm_le ξ
    exact hb.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound (S.comp P.range.subtypeL)
      (norm_nonneg (S.comp P))
    intro ξ
    have hb := (S.comp P).le_opNorm (ξ : H)
    simpa only [ContinuousLinearMap.comp_apply, projection_fixed_on_range P hP,
      Submodule.subtypeL_apply, Submodule.norm_coe] using hb

theorem projection_norm_equality_no_spectral_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (hPn : P ≠ 0)
    (Q : K →L[ℂ] K) (hQ : IsStarProjection Q)
    (R : H →L[ℂ] K) (A : K →L[ℂ] E)
    (hnorm : ‖Q.comp (R.comp P)‖ = ‖R.comp P‖)
    {t : ℝ} (ht : 0 < t)
    (hlower : ∀ ξ, t * ‖P ξ‖ ^ 2 ≤ ‖A (R (P ξ) - Q (R (P ξ)))‖ ^ 2) : False := by
  have hex : ∃ ξ, P ξ ≠ 0 := by
    by_contra h
    apply hPn
    ext ξ
    simpa using not_exists.mp h ξ
  obtain ⟨ξ, hξ⟩ := hex
  let x : P.range := ⟨P ξ, ⟨ξ, rfl⟩⟩
  let : Nontrivial P.range := nontrivial_of_ne x 0 (fun he => hξ (congrArg Subtype.val he))
  have he : ‖Q.comp (R.comp P.range.subtypeL)‖ = ‖R.comp P.range.subtypeL‖ := by
    have h := norm_comp_projection_eq_norm_restrict P hP (Q.comp R)
    have hg := norm_comp_projection_eq_norm_restrict P hP R
    rw [ContinuousLinearMap.comp_assoc] at h
    exact h.symm.trans (hnorm.trans hg)
  apply norm_preserving_projection_no_coercive_complement
    (R.comp P.range.subtypeL) Q hQ A he ht
  intro η
  have h := hlower (η : H)
  simpa only [projection_fixed_on_range P hP, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.norm_coe] using h

end

end KadisonKastler

end OAI
