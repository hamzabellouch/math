import OAI.Analysis.CircleDomains.Transfer.ModelSelectedBounds
import OAI.Analysis.CircleDomains.Transfer.ModelPairWorkingError

namespace OAI

/-! The selected compact pair has a uniform trace bound, obtained from
the actual omitted set and controlled-height closeness. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_norm_le (a b : ℝ) : ‖planePair a b‖ ≤ |a|+|b| := by
  have he : ‖planePair a b‖^2 = a^2+b^2 := by simp only [plane_norm_sq, planePair_zero, planePair_one]
  nlinarith [norm_nonneg (planePair a b), abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_pair_trace_bound (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d A L δ ε C v : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε)
    (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    (hH : ∀ z ∈ closedBall 0 C, |H.height z-z.im| ≤ v)
    (η : ℂ → ℝ) (hη : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1)
    (θ : EuclideanPlane → ℝ)
    (hθ : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1)
    {z : ℂ} (hz : (z : Sphere) ∉ G) :
    ‖planePair
      (sphereFromPlaneFunction (M.compactPrioritySource S.cutoff S.value η) (z : Sphere))
      (sphereFromPlaneFunction (M.compactHeightSource H (flattenValues S.heightValues) θ) (z : Sphere))‖
      ≤ 2*C+δ+v := by
  have hp := S.priority_trace_bound M hsard hsch hG hconn hinf hTD hC hz
  have hp' : |sphereFromPlaneFunction (M.compactPrioritySource S.cutoff S.value η) (z : Sphere)| ≤ C := by
    simpa only [sphereFromPlaneFunction_coe, compactPrioritySource,
      complexPlaneCoordinates.apply_symm_apply, hη z hz, one_mul, Real.norm_eq_abs] using hp
  have hqeq : sphereFromPlaneFunction (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (z : Sphere) = flattenValues S.heightValues (M.heightSection H (z : Sphere)) := by
    simpa only [sphereFromPlaneFunction_coe, compactHeightSource, planeSphere,
      complexPlaneCoordinates.apply_symm_apply] using
        M.compact_height_trace hsard hsch hG hconn hinf hTD H (flattenValues S.heightValues) θ hθ hz
  have hfinite := M.finiteCoord_bound_of_projection_outside hinf hC
    (show M.projection (invFun M.projection (z : Sphere)) ∉ G from by
      rw [(M.section_target_complement hsard hsch hG hconn hinf hTD hz).2.2]
      exact hz)
  have hh := hH (finiteCoord (invFun M.projection (z : Sphere)))
    (mem_closedBall_zero_iff.mpr hfinite)
  have hy := Complex.abs_im_le_norm (finiteCoord (invFun M.projection (z : Sphere)))
  have hheight : |M.heightSection H (z : Sphere)| ≤ v+C := by
    have ht := abs_sub_le (H.height (finiteCoord (invFun M.projection (z : Sphere))))
      (finiteCoord (invFun M.projection (z : Sphere))).im 0
    simp only [sub_zero, heightSection] at *
    linarith
  have hq' : |sphereFromPlaneFunction (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (z : Sphere)| ≤ δ+v+C := by
    rw [hqeq]
    have ht := abs_sub_le (flattenValues S.heightValues (M.heightSection H (z : Sphere)))
      (M.heightSection H (z : Sphere)) 0
    simp only [sub_zero] at ht
    linarith [S.height_close (M.heightSection H (z : Sphere))]
  exact (planePair_norm_le _ _).trans (by linarith)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
