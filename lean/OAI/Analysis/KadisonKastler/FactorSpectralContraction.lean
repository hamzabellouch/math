import OAI.Analysis.KadisonKastler.SpectralHalfBounds

namespace OAI

/-! # A uniform spectral contraction in every factor -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
private theorem apply_real_smul (A : FiniteInnerAverage M) (r : ℝ)
    (x : H →L[ℂ] H) : A.apply (r • x) = r • A.apply x :=
  (A.linear.restrictScalars ℝ).map_smul r x

omit [Nontrivial H] in
private theorem apply_real_scalar (A : FiniteInnerAverage M) (r : ℝ) :
    A.apply (r • (1 : H →L[ℂ] H)) = r • (1 : H →L[ℂ] H) := by
  simpa only [Complex.coe_smul] using A.apply_scalar (r : ℂ)

/-- The midpoint of a scalar order interval is within half its length. -/
theorem norm_sub_midpoint_le (x : H →L[ℂ] H) (hx : IsSelfAdjoint x)
    (a b : ℝ) (hl : a • (1 : H →L[ℂ] H) ≤ x)
    (hu : x ≤ b • (1 : H →L[ℂ] H)) :
    ‖x - ((a + b) / 2) • (1 : H →L[ℂ] H)‖ ≤ (b - a) / 2 := by
  have hc : IsSelfAdjoint (((a + b) / 2) • (1 : H →L[ℂ] H)) := by
    change star (((a + b) / 2) • (1 : H →L[ℂ] H)) = _
    simp only [star_smul, star_trivial, star_one]
  apply norm_le_of_symmetric_scalar_bounds _ (hx.sub hc) ((b - a) / 2)
  · have h := sub_le_sub_right hl (((a + b) / 2) • (1 : H →L[ℂ] H))
    have he : a • (1 : H →L[ℂ] H) - ((a + b) / 2) • 1 =
        -(algebraMap ℝ (H →L[ℂ] H) ((b - a) / 2)) := by
      rw [← sub_smul, Algebra.algebraMap_eq_smul_one, ← neg_smul]
      congr 1
      ring
    rwa [he] at h
  · have h := sub_le_sub_right hu (((a + b) / 2) • (1 : H →L[ℂ] H))
    have he : b • (1 : H →L[ℂ] H) - ((a + b) / 2) • 1 =
        algebraMap ℝ (H →L[ℂ] H) ((b - a) / 2) := by
      rw [← sub_smul, Algebra.algebraMap_eq_smul_one]
      congr 1
      ring
    rwa [he] at h

/-- Projection comparison shrinks the norm radius of a self-adjoint operator
by three quarters after subtracting a real scalar. -/
theorem exists_factor_spectral_contraction (hM : ScalarCenter M)
    (x : Algebra M) (hx : IsSelfAdjoint x) :
    ∃ (A : FiniteInnerAverage M) (c : ℝ),
      ‖A.apply x.val - c • (1 : H →L[ℂ] H)‖ ≤ (3 / 4 : ℝ) * ‖x‖ := by
  let p := positiveSupport x
  let q : AlgebraProjection M := ⟨1 - p.val, p.property.one_sub⟩
  have hf : ∀ z : Algebra M, (∀ a : Algebra M, a * z = z * a) →
      ∃ c : ℂ, z = c • (1 : Algebra M) := by
    intro z hz
    obtain ⟨c, hc⟩ := hM z.val z.property (fun a ha =>
      congrArg Subtype.val (hz ⟨a, ha⟩))
    exact ⟨c, Subtype.ext hc⟩
  have hSA : IsSelfAdjoint x.val := congrArg Subtype.val hx
  have hn : ‖x.val‖ = ‖x‖ := rfl
  have hglobalLo : (-‖x‖) • (1 : H →L[ℂ] H) ≤ x.val := by
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul, hn] using hSA.neg_algebraMap_norm_le_self
  have hglobalHi : x.val ≤ ‖x‖ • (1 : H →L[ℂ] H) := by
    simpa only [Algebra.algebraMap_eq_smul_one, hn] using hSA.le_algebraMap_norm_self
  have hbounds := spectral_half_bounds x hx
  rcases AlgebraProjection.subequivalent_total hf p q with hp | hq
  · obtain ⟨A, hA⟩ := exists_projection_half_average p hp
    have hhi : A.apply x.val ≤ (‖x‖ / 2) • (1 : H →L[ℂ] H) := by
      have h := A.apply_mono hbounds.1
      rw [apply_real_smul] at h
      have hA' : A.apply p.val.val ≤ (1 / 2 : ℝ) • (1 : H →L[ℂ] H) := by
        simpa only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat] using hA
      apply h.trans
      convert smul_le_smul_of_nonneg_left hA' (norm_nonneg x) using 1;
        simp only [smul_smul]; congr 1; ring
    have hlo := A.apply_mono hglobalLo
    rw [apply_real_scalar] at hlo
    have hs : IsSelfAdjoint (A.apply x.val) := by
      rw [← A.algebraApply_val]
      exact congrArg Subtype.val (A.algebraApply_selfAdjoint x hx)
    refine ⟨A, (-‖x‖ + ‖x‖ / 2) / 2, ?_⟩
    have h := norm_sub_midpoint_le _ hs _ _ hlo hhi
    convert h using 1; ring
  · have hqp : q.Subequivalent (⟨1 - q.val, q.property.one_sub⟩ : AlgebraProjection M) := by
      have he : (⟨1 - q.val, q.property.one_sub⟩ : AlgebraProjection M) = p := by
        apply Subtype.ext
        change 1 - (1 - p.val) = p.val
        abel
      rwa [he]
    obtain ⟨A, hA⟩ := exists_projection_half_average q hqp
    have hlo : (-‖x‖ / 2) • (1 : H →L[ℂ] H) ≤ A.apply x.val := by
      have h := A.apply_mono hbounds.2
      rw [show -(‖x‖ • (1 - p.val.val)) = (-‖x‖) • (1 - p.val.val) by rw [neg_smul],
        apply_real_smul] at h
      have hA' : A.apply q.val.val ≤ (1 / 2 : ℝ) • (1 : H →L[ℂ] H) := by
        simpa only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat] using hA
      have hn := smul_le_smul_of_nonpos_left hA' (neg_nonpos.mpr (norm_nonneg x))
      apply le_trans _ h
      convert hn using 1; simp only [smul_smul]; congr 1; ring
    have hhi := A.apply_mono hglobalHi
    rw [apply_real_scalar] at hhi
    have hs : IsSelfAdjoint (A.apply x.val) := by
      rw [← A.algebraApply_val]
      exact congrArg Subtype.val (A.algebraApply_selfAdjoint x hx)
    refine ⟨A, (-‖x‖ / 2 + ‖x‖) / 2, ?_⟩
    have h := norm_sub_midpoint_le _ hs _ _ hlo hhi
    convert h using 1; ring

end

end KadisonKastler

end OAI
