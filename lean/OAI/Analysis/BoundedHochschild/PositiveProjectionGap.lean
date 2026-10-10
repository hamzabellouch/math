import OAI.Analysis.BoundedHochschild.SpectralProjections

namespace OAI

/-! A nonzero positive element dominates a positive multiple of a nonzero
projection. This is the small spectral-cut consequence needed for the
minimal averaging argument. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_positive_projection_gap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {a : M} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ p : M, IsStarProjection p ∧ p ≠ 0 ∧ ∃ δ : ℝ, 0 < δ ∧ δ • p ≤ a := by
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b := ‖a‖⁻¹ • a
  have hb : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖ = 1 := by
    rw [show b = ‖a‖⁻¹ • a from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨p, hp, hlow, hupp⟩ := HochschildSakai.exists_dyadic_projection e b hb
    ((CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn.le)
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, sub_zero] at hupp
    have hnn := (CStarAlgebra.norm_le_one_iff_of_nonneg ((2 : ℝ) • b)
      (smul_nonneg (by norm_num) hb)).mpr hupp
    rw [norm_smul, hbn, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hnn
    norm_num at hnn
  refine ⟨p, hp, hp0, ‖a‖ / 2, half_pos hn, ?_⟩
  have hh := smul_le_smul_of_nonneg_left (sub_nonneg.mp hlow) (le_of_lt (half_pos hn))
  have he : (‖a‖ / 2) • ((2 : ℝ) • b) = a := by
    dsimp [b]
    rw [smul_smul, smul_smul]
    have hc : (‖a‖ / 2) * 2 * ‖a‖⁻¹ = 1 := by field_simp
    rw [hc, one_smul]
  rwa [he] at hh

lemma projection_le_of_positive_gap {p q a : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {δ : ℝ} (hδ : 0 < δ) (hgap : δ • p ≤ a) (haq : a * (1 - q) = 0) : p ≤ q := by
  have hh := star_left_conjugate_le_conjugate hgap (1 - q)
  have hs : star (p * (1 - q)) * (p * (1 - q)) =
      star (1 - q) * p * (1 - q) := by
    simp only [star_mul, hp.isSelfAdjoint.star_eq, ← mul_assoc]
    rw [mul_assoc (star (1 - q)) p p, hp.isIdempotentElem.eq]
  have hz : δ • (star (p * (1 - q)) * (p * (1 - q))) ≤ 0 := by
    rw [hs]
    simpa only [star_sub, star_one,
      hq.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc, mul_assoc,
      hp.isIdempotentElem.eq, haq, mul_zero] using hh
  have he : star (p * (1 - q)) * (p * (1 - q)) = 0 :=
    le_antisymm ((smul_nonpos_iff_nonpos_of_pos_left hδ).mp hz) (star_mul_self_nonneg _)
  have hpq := (CStarRing.star_mul_self_eq_zero_iff _).mp he
  apply (hp.le_iff_mul_eq_left hq).mpr
  simpa only [mul_sub, mul_one, sub_eq_zero, eq_comm] using hpq

end BoundedHochschild.KadisonRingrose

end

end OAI
