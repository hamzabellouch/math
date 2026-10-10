import OAI.Geometry.SurfaceImmersion.Atlas.RegularPlaneChart
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCurve

namespace OAI

/-! Replacing the longitudinal coordinate by a smooth function with
unit axial derivative is an actual local plane diffeomorphism. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def timeCoordinateMap (φ : Base → ℝ) (x : Base) : Base := ![x 0,φ x]

lemma timeCoordinateMap_smooth {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (timeCoordinateMap φ) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [timeCoordinateMap] using contDiff_apply ℝ ℝ (0:Fin 2)
  · simpa [timeCoordinateMap] using hφ

lemma timeCoordinateMap_regular {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : Base) (hvertical : fderiv ℝ φ p (crosscapAxis 1) = 1) :
    Function.Bijective (fderiv ℝ (timeCoordinateMap φ) p) := by
  let D : Base →L[ℝ] Base := ContinuousLinearMap.pi ![ContinuousLinearMap.proj (0:Fin 2),fderiv ℝ φ p]
  have hD : HasFDerivAt (timeCoordinateMap φ) D p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasFDerivAt_apply (𝕜 := ℝ) 0 p
    · exact (hφ.differentiable (by simp) p).hasFDerivAt
  rw [hD.fderiv]
  have hi : Function.Injective D := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro v hv
      have hv0 : v 0 = 0 := congrFun hv 0
      have hvφ : fderiv ℝ φ p v = 0 := congrFun hv 1
      have he : v = (v 1) • crosscapAxis 1 := by
        ext i
        fin_cases i <;> simp [crosscapAxis_apply,hv0]
      have hv1 : v 1 = 0 := by
        rw [he,map_smul,hvertical] at hvφ
        simpa only [smul_eq_mul,mul_one] using hvφ
      show v = 0
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    · exact bot_le
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := D.toLinearMap) rfl).mp hi⟩

theorem triangular_time_coordinates {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : Base) (hvertical : fderiv ℝ φ p (crosscapAxis 1) = 1) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (e : Base → Base) = timeCoordinateMap φ ∧ ContDiffOn ℝ ∞ e.symm e.target :=
  regular_plane_chart (timeCoordinateMap_smooth hφ) p (timeCoordinateMap_regular hφ p hvertical)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
