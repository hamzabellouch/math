import OAI.Analysis.CircleDomains.Selection.NearMaximalHeightSelection
import OAI.Analysis.CircleDomains.Transfer.ModelLocalizedSelection
import OAI.Analysis.CircleDomains.Selection.SelectedHeightError

namespace OAI

/-! Choose the actual model, height, common flattenings and priority
supports after fixing the cutoff constants and the desired energy budget. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_small_selected_height_data
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hne : Nonempty (CompactScalarModel G u))
    {R C : ℝ} (hR : 0 < R) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G)
    (hC : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 C)
    (A L : ℝ) (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hsθ : HasCompactSupport θ) (hθA : tsupport θ ⊆ ball 0 A)
    {Cθ : ℝ} (hCθ : 0 ≤ Cθ) (hθunit : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθd : ∀ x, ‖fderiv ℝ θ x‖ ≤ Cθ)
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    ∃ e : ℝ, 0 < e ∧ e < b ∧ ∃ d : ℝ, 0 < d ∧ d < e ∧
      ∃ M : CompactScalarModel G u, ∃ H : ControlledHeight (3*R+1) d,
      ∃ S : CompactScalarModel.FlattenedSourceSelection M H Wold A L e e,
        (∀ z ∈ closedBall 0 A, |H.height z-z.im| < e) ∧
        (∀ n, support (S.cutoff n) ⊆ ball 0 C) ∧
        ∃ E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
          (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
          (physicalPlaneDomain G),
          (∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
            heightLimitGradient H.error₀ H.error₁ x = 0) ∧
          (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) < t^2 := by
  obtain ⟨e,he,heb,hbudget⟩ := exists_height_error_scale 1 Cθ
    (volume (ball (0 : EuclideanPlane) A)).toReal ht hb
  obtain ⟨d,hd,hde,M,H,hHz,hclose⟩ := exists_close_model_height hsolver hprincipal hgreen harea
    hG hinf hu hs hne hR hsource (isCompact_closedBall (0 : ℂ) A) he he
  obtain ⟨S,hS⟩ := M.exists_flattened_source_selection_in_ball hsard hsch hcoarea
    hG hconn hinf hTD hB hBne hC hu hs Wold H hHz A L he he
  have hclose' : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ e := by
    intro x hx
    have hz : complexPlaneCoordinates x ∈ closedBall (0 : ℂ) A := by
      simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using
        (show ‖x‖ ≤ A from (mem_ball_zero_iff.mp hx).le)
    exact (hclose _ hz).le
  have hbudget' : 2*(2*e+4*Real.pi*e)+4*Cθ^2*(e+e)^2*
      (volume (ball (0 : EuclideanPlane) A)).toReal < t^2 := by
    simpa only [one_pow, mul_one] using hbudget
  obtain ⟨E,hE⟩ := S.exists_small_height_error M hG hinf H he hde.le θ hθ hsθ hθA
    hCθ hθunit hθd hclose' hbudget'
  exact ⟨e,he,heb,d,hd,hde,M,H,S,hclose,hS,E,hHz,hE⟩

end CircleDomainRigidity

end

end OAI
