import OAI.Geometry.SurfaceImmersion.Atlas.AtlasNormalProjectionBounds
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection

namespace OAI

/-! Quantitative normalization of the atlas projection on an exterior open set. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

lemma radialNormalize_unit {u : Space} (hu : u ≠ 0) : ‖radialNormalize u‖ = 1 := by
  rw [radialNormalize,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

lemma radialNormalize_sub_unit_bound {u v : Space} (hu : u ≠ 0) (hv : ‖v‖ = 1) :
    ‖radialNormalize u-v‖ ≤ 2*‖u-v‖ := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he : ‖radialNormalize u-u‖ = |1-‖u‖| := by
    have he : ‖u‖⁻¹ • u-u = (‖u‖⁻¹-1) • u := by rw [sub_smul,one_smul]
    rw [radialNormalize,he,norm_smul,Real.norm_eq_abs]
    calc
      |‖u‖⁻¹-1| *‖u‖ = |(‖u‖⁻¹-1)*‖u‖| := by rw [abs_mul,abs_of_nonneg hn.le]
      _ = |1-‖u‖| := by congr 1; field_simp
  have habs : |1-‖u‖| ≤ ‖u-v‖ := by
    rw [abs_sub_comm,← hv]
    exact abs_norm_sub_norm_le u v
  calc
    ‖radialNormalize u-v‖ ≤ ‖radialNormalize u-u‖+‖u-v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*‖u-v‖ := by rw [he]; linarith

end ClosedSurfaceR4.SphericalJets
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def unitProjectedNormalField (F n : M → Space) : M → Space :=
  SphericalJets.radialNormalize ∘ A.projectedNormalField F n

theorem unitProjectedNormalField_properties {F n : M → Space} {U : Set M}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0)
    (hne : ∀ p ∈ U, A.projectedNormalField F n p ≠ 0) :
    ContMDiffOn planeModel spaceModel ∞ (A.unitProjectedNormalField F n) U ∧
      (∀ p ∈ U, ‖A.unitProjectedNormalField F n p‖ = 1) ∧
      (∀ p ∈ U, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential F p v) (A.unitProjectedNormalField F n p) = 0) := by
  have hP := A.projectedNormalField_smooth hF hn hD
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact ((SphericalJets.radialNormalize_smoothAt (hne p hp)).contMDiffAt.comp p (hP p)).contMDiffWithinAt
  · intro p hp
    exact SphericalJets.radialNormalize_unit (hne p hp)
  · intro p hp v
    change inner ℝ (surfaceDifferential F p v)
      (‖A.projectedNormalField F n p‖⁻¹ • A.projectedNormalField F n p) = 0
    have hh := A.projectedNormalField_normal hF n hD p v
    change inner ℝ (surfaceDifferential F p v) (A.projectedNormalField F n p) = 0 at hh
    rw [real_inner_smul_right,hh,mul_zero]

omit [CompactSpace M] in
theorem unitProjectedNormalField_sub_bound {F n : M → Space} {p : M} {δ : ℝ}
    (hn : ‖n p‖ = 1) (hδ : δ < 1)
    (hlocal : ∀ i : A.centers, A.weight i p ≠ 0 →
      ‖A.chartProjectedNormal i F n p - n p‖ ≤ δ) :
    A.projectedNormalField F n p ≠ 0 ∧
      ‖A.unitProjectedNormalField F n p-n p‖ ≤ 2*δ := by
  have hb := A.projectedNormalField_sub_bound F n p hlocal
  have hne := A.projectedNormalField_ne_zero F n p hn (hb.trans_lt hδ)
  exact ⟨hne,(SphericalJets.radialNormalize_sub_unit_bound hne hn).trans
    (mul_le_mul_of_nonneg_left hb (by norm_num))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
