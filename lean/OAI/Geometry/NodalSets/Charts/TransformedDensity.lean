import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Determinant
import OAI.Geometry.NodalSets.Charts.PositiveMetric
import OAI.Geometry.NodalSets.Elliptic.LocalSpatialJet

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def coordDet (J : Coord →L[ℝ] Coord) : ℝ :=
  Matrix.det (fun i j : Fin 4 ↦ (J (Pi.single j 1)) i)

lemma coordDet_smooth : ContDiff ℝ ∞ coordDet := by
  have hdet : coordDet = fun J : Coord →L[ℝ] Coord ↦
      ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, J (Pi.single i 1) (σ i) := by
    funext J
    exact Matrix.det_apply' _
  rw [hdet]
  apply ContDiff.sum
  intro sigma _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (ContinuousLinearMap.proj (sigma i) : Coord →L[ℝ] ℝ).contDiff.comp
    (contDiff_id.clm_apply contDiff_const)

lemma coordDet_equiv_ne_zero (J : Coord ≃L[ℝ] Coord) : coordDet J.toContinuousLinearMap ≠ 0 := by
  change (LinearMap.toMatrix' J.toLinearEquiv.toLinearMap).det ≠ 0
  rw [LinearMap.det_toMatrix']
  exact J.toLinearEquiv.isUnit_det'.ne_zero

def chartDensity (w : Coord → ℝ) (p : QuadParam Coord) (x : Coord) : ℝ :=
  w (rawQuadratic p x) * |coordDet (fderiv ℝ (rawQuadratic p) x)|

lemma chartDensity_pos (w : Coord → ℝ) (p : QuadParam Coord) (x : Coord)
    (hw : 0 < w (rawQuadratic p x)) (J : Coord ≃L[ℝ] Coord)
    (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    0 < chartDensity w p x := by
  unfold chartDensity
  rw [hJ]
  exact mul_pos hw (abs_pos.mpr (coordDet_equiv_ne_zero J))

theorem chartDensity_smooth_at (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam Coord) (x : Coord) (J : Coord ≃L[ℝ] Coord)
    (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    ContDiffAt ℝ ∞ (Function.uncurry (chartDensity w)) (p,x) := by
  have hdet := coordDet_smooth.comp (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth)
  have hn : coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0 := by
    rw [hJ]; exact coordDet_equiv_ne_zero J
  exact (hw.comp rawQuadratic_smooth).contDiffAt.mul (hdet.contDiffAt.abs hn)

lemma pulledForm_positive (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    ∀ v, v ≠ 0 → 0 < pulledForm g p x v v := by
  intro v hv
  change 0 < g (rawQuadratic p x) (fderiv ℝ (rawQuadratic p) x v) (fderiv ℝ (rawQuadratic p) x v)
  rw [hJ]
  exact hp (J v) (by intro hz; exact hv (J.injective (by simpa using hz)))

end
end Yau.Geometry

end OAI
