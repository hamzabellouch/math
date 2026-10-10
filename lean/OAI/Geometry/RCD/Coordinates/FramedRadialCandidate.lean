import OAI.Geometry.RCD.Coordinates.FramedPointValues
import OAI.Geometry.RCD.Coordinates.CovectorRadialSmallness

namespace OAI

/-! # The actual centered coordinate candidate for the radial fit -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  (hQ : QuadraticCheegerEnergy μ)

/-- The qualitative radial estimate controls the specific original
centered coordinate candidate, rather than just the best-fit infimum. -/
theorem DyadicDistanceReplacements.framed_radial_candidate
    {n : ℕ} {κ r0 B J C ε Cχ : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ)
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (V W : X → Euclidean n)
    (hV : ContinuousOn V (ball p (4 * (distanceSourceRadius r0 i / 64))))
    (hu : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[
      μ.restrict (ball p (4 * (distanceSourceRadius r0 i / 64)))] fun x => V x j)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * (distanceSourceRadius r0 i / 64)) ε
      (transformedColumn μ hQ u N) W)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 ε
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (W x - W p)))
    (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[
      μ.restrict (ball p (4 * (distanceSourceRadius r0 i / 64)))] fun _ => (1 : ℝ))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < μ.real (ball p (4 * (distanceSourceRadius r0 i / 64))))
    (b : Euclidean n) :
    let r := distanceSourceRadius r0 i / 64
    (∫ x in ball p r,
      (localGamma μ hQ (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) x -
        SobolevSpace.toLp μ hQ (centeredAffineSobolev μ hQ u η (V p) b) x) ^ 2 ∂μ) ≤
      (n : ℝ) * ((1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1)) * ε * r ^ 2 *
        μ.real (ball p (4 * r))) * ‖N.symm b‖ ^ 2 := by
  dsimp only
  let r := distanceSourceRadius r0 i / 64
  have hr : 0 < r := div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)
  let uN := transformedColumn μ hQ u N
  let uC := centeredColumn μ hQ uN (W p) η
  have hcenter := framed_covector_point_values μ hQ u N (ball p (4 * r)) isOpen_ball
    V W hV hfirst.continuous hu hfirst.representative b (mem_ball_self (by positivity))
  have hcolumn := centered_frame_covector_eq μ hQ u N η (V p) (W p) b hcenter
  have hcentered := hfirst.center μ hQ (W p) η hη
  have herr := T.local_covector_radial_error μ hQ i hε hε1 hCχ uC
    (fun x => W x - W p) hcentered (sub_self _) hmetric χ hvol (N.symm b)
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have hconst := centeredColumn_covector_difference μ hQ uN (ball p r)
    (W p) (N.symm b) η (ae_restrict_of_ae_restrict_of_subset hsub hη)
  have hg := localGamma_eq_of_constant_difference μ hQ (ball p r)
    (sobolevColumnMap μ hQ uC (N.symm b)) (sobolevColumnMap μ hQ uN (N.symm b))
    (T.distanceDatum μ hQ i) (-⟪W p, N.symm b⟫_ℝ) hconst
  have huN : sobolevColumnMap μ hQ uN (N.symm b) = sobolevColumnMap μ hQ u b := by
    simp only [uN, sobolevColumnMap_transformed, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [huN] at hg
  have heq : (∫ x in ball p r,
      (localGamma μ hQ (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) x -
        SobolevSpace.toLp μ hQ (centeredAffineSobolev μ hQ u η (V p) b) x) ^ 2 ∂μ) =
      ∫ x in ball p r,
        (localGamma μ hQ (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ uC (N.symm b)) x -
          SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ uC (N.symm b)) x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg,
      ae_restrict_of_ae (localGamma_comm μ hQ (T.distanceDatum μ hQ i)
        (sobolevColumnMap μ hQ u b)),
      ae_restrict_of_ae (localGamma_comm μ hQ (T.distanceDatum μ hQ i)
        (sobolevColumnMap μ hQ uC (N.symm b)))] with x hx h₁ h₂
    rw [h₂, hx, ← h₁, show sobolevColumnMap μ hQ uC (N.symm b) =
      centeredAffineSobolev μ hQ u η (V p) b from hcolumn]
  rw [heq]
  exact herr

end RegularPointCoordinates

end

end OAI
