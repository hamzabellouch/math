import OAI.Analysis.KadisonKastler.CentralProjectionAveraging
import OAI.Analysis.KadisonKastler.FactorSpectralContraction

namespace OAI

/-! # Uniform contraction toward the center of a von Neumann algebra -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
private theorem average_real_smul (A : FiniteInnerAverage M) (r : ℝ)
    (x : H →L[ℂ] H) : A.apply (r • x) = r • A.apply x :=
  (A.linear.restrictScalars ℝ).map_smul r x

omit [Nontrivial H] in
private theorem spectral_average_upper (x : Algebra M) (hx : IsSelfAdjoint x)
    (A : FiniteInnerAverage M) (z : H →L[ℂ] H)
    (hp : A.apply (positiveSupport x).val.val ≤ (1 / 2 : ℝ) • (1 + z)) :
    A.apply x.val ≤ (‖x‖ / 2 : ℝ) • (1 + z) := by
  have h := A.apply_mono (spectral_half_bounds x hx).1
  rw [average_real_smul] at h
  apply h.trans
  convert smul_le_smul_of_nonneg_left hp (norm_nonneg x) using 1;
    simp only [smul_smul]; congr 1; ring

omit [Nontrivial H] in
private theorem spectral_average_lower (x : Algebra M) (hx : IsSelfAdjoint x)
    (A : FiniteInnerAverage M) (z : H →L[ℂ] H)
    (hq : A.apply (1 - (positiveSupport x).val.val) ≤
      (1 / 2 : ℝ) • (2 • (1 : H →L[ℂ] H) - z)) :
    (-‖x‖ / 2 : ℝ) • (2 • (1 : H →L[ℂ] H) - z) ≤ A.apply x.val := by
  have h := A.apply_mono (spectral_half_bounds x hx).2
  rw [show -(‖x‖ • (1 - (positiveSupport x).val.val)) =
    (-‖x‖) • (1 - (positiveSupport x).val.val) by rw [neg_smul], average_real_smul] at h
  apply le_trans _ h
  convert smul_le_smul_of_nonpos_left hq (neg_nonpos.mpr (norm_nonneg x)) using 1;
    simp only [smul_smul]; congr 1; ring

private theorem central_interval_norm_bound (t z : H →L[ℂ] H)
    (ht : IsSelfAdjoint t) (hz : IsSelfAdjoint z) (R : ℝ)
    (hl : (-R / 2) • (2 • (1 : H →L[ℂ] H) - z) ≤ t)
    (hu : t ≤ (R / 2) • (1 + z)) :
    ‖t - (R / 4) • (2 • z - 1)‖ ≤ (3 / 4 : ℝ) * R := by
  have hc : IsSelfAdjoint ((R / 4) • (2 • z - 1)) := by
    change star ((R / 4) • (2 • z - 1)) = (R / 4) • (2 • z - 1)
    simp only [star_smul, star_trivial, star_sub, star_one, hz.star_eq]
  apply norm_le_of_symmetric_scalar_bounds _ (ht.sub hc)
  · have h := sub_le_sub_right hl ((R / 4) • (2 • z - 1))
    have he : (-R / 2) • (2 • (1 : H →L[ℂ] H) - z) - (R / 4) • (2 • z - 1) =
        -(algebraMap ℝ (H →L[ℂ] H) ((3 / 4 : ℝ) * R)) := by
      rw [Algebra.algebraMap_eq_smul_one]
      module
    rwa [he] at h
  · have h := sub_le_sub_right hu ((R / 4) • (2 • z - 1))
    have he : (R / 2) • (1 + z) - (R / 4) • (2 • z - 1) =
        algebraMap ℝ (H →L[ℂ] H) ((3 / 4 : ℝ) * R) := by
      rw [Algebra.algebraMap_eq_smul_one]
      module
    rwa [he] at h

/-- A central sign projection selects the midpoint of the reduced spectral
interval. The contraction is uniform in the algebra and representation. -/
theorem exists_central_spectral_contraction (x : Algebra M) (hx : IsSelfAdjoint x) :
    ∃ (A : FiniteInnerAverage M) (c : Algebra (concreteCenter M)),
      IsSelfAdjoint c ∧
      ‖A.apply x.val - c.val‖ ≤ (3 / 4 : ℝ) * ‖x‖ := by
  obtain ⟨A, z, hz, hp, hq⟩ := exists_central_projection_average (positiveSupport x)
  let zC : Algebra (concreteCenter M) := ⟨z.val.val, z.val.property, by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact congrArg Subtype.val (hz ⟨a, ha⟩)⟩
  have hzC : IsSelfAdjoint zC := by
    apply Subtype.ext
    exact congrArg (fun a : Algebra M => a.val) z.property.isSelfAdjoint.star_eq
  let c : Algebra (concreteCenter M) := (‖x‖ / 4 : ℝ) • (2 • zC - 1)
  have hc : IsSelfAdjoint c := by
    change star ((‖x‖ / 4 : ℝ) • (2 • zC - 1)) = (‖x‖ / 4 : ℝ) • (2 • zC - 1)
    simp only [star_smul, star_trivial, star_sub, star_one, hzC.star_eq]
  have hs : IsSelfAdjoint (A.apply x.val) := by
    rw [← A.algebraApply_val]
    exact congrArg (fun a : Algebra M => a.val) (A.algebraApply_selfAdjoint x hx)
  have hzAmbient : IsSelfAdjoint z.val.val :=
    congrArg (fun a : Algebra M => a.val) z.property.isSelfAdjoint.star_eq
  have hcval : c.val = (‖x‖ / 4 : ℝ) • (2 • z.val.val - 1) := rfl
  refine ⟨A, c, hc, ?_⟩
  rw [hcval]
  exact central_interval_norm_bound _ _ hs hzAmbient
    ‖x‖ (spectral_average_lower x hx A z.val.val hq) (spectral_average_upper x hx A z.val.val hp)

end

end KadisonKastler

end OAI
