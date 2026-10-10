import OAI.Geometry.SurfaceImmersion.Atlas.CenteredAtlasDifferentials
import OAI.Geometry.SurfaceImmersion.Correction.CircularSmoothingAtlas
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace OAI

/-! Explicit regular parametrizations of the actual coordinate circles.
The compact parameter interval covers the whole boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def circularParam (c : CurvePlane) (r t : ℝ) : CurvePlane :=
  (c.1+r*Real.cos t,c.2+r*Real.sin t)

def circularVelocity (r t : ℝ) : CurvePlane := (-r*Real.sin t,r*Real.cos t)

lemma circularParam_smooth (c : CurvePlane) (r : ℝ) : ContDiff ℝ ∞ (circularParam c r) := by
  change ContDiff ℝ ∞ (fun t => (c.1+r*Real.cos t,c.2+r*Real.sin t))
  fun_prop

lemma circularParam_hasDerivAt (c : CurvePlane) (r t : ℝ) :
    HasDerivAt (circularParam c r) (circularVelocity r t) t := by
  have h := ((Real.hasDerivAt_cos t).const_mul r |>.const_add c.1).prodMk
    ((Real.hasDerivAt_sin t).const_mul r |>.const_add c.2)
  have he : circularVelocity r t = (r*(-Real.sin t),r*Real.cos t) := by
    simp only [circularVelocity, mul_neg, neg_mul]
  rw [he]
  exact h

lemma circularVelocity_ne_zero {r : ℝ} (hr : r ≠ 0) (t : ℝ) : circularVelocity r t ≠ 0 := by
  intro he
  have hs : Real.sin t = 0 := (mul_eq_zero.mp (congrArg Prod.fst he)).resolve_left (neg_ne_zero.mpr hr)
  have hc : Real.cos t = 0 := (mul_eq_zero.mp (congrArg Prod.snd he)).resolve_left hr
  have h := Real.sin_sq_add_cos_sq t
  simp [hs,hc] at h

lemma circularParam_radius (c : CurvePlane) (r t : ℝ) :
    circularRadiusSquared c (circularParam c r t) = r^2 := by
  dsimp [circularRadiusSquared,circularParam]
  nlinarith [Real.sin_sq_add_cos_sq t]

lemma circularParam_covers {c x : CurvePlane} {r : ℝ} (hr : 0 < r)
    (hx : circularRadiusSquared c x = r^2) :
    ∃ t ∈ Icc (-Real.pi) Real.pi, circularParam c r t = x := by
  let z : ℂ := ⟨x.1-c.1,x.2-c.2⟩
  have hn : ‖z‖ = r := by
    have hs : ‖z‖^2 = r^2 := by
      rw [Complex.sq_norm]
      simpa [Complex.normSq_apply,z,circularRadiusSquared,pow_two] using hx
    nlinarith [norm_nonneg z]
  refine ⟨z.arg,⟨(Complex.neg_pi_lt_arg z).le,Complex.arg_le_pi z⟩,?_⟩
  have hcos := Complex.norm_mul_cos_arg z
  have hsin := Complex.norm_mul_sin_arg z
  rw [hn] at hcos hsin
  apply Prod.ext <;> dsimp [circularParam]
  · dsimp [z] at hcos
    linarith
  · dsimp [z] at hsin
    linarith

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularBoundary (p : M) (r : ℝ) : Set M :=
  (coordinateChart p).source ∩ (coordinateChart p) ⁻¹'
    {x | circularRadiusSquared (coordinateChart p p) x = r^2}

def circularBoundaryParam (p : M) (r : ℝ) (t : ℝ) : M :=
  (coordinateChart p).symm (circularParam (coordinateChart p p) r t)

omit [IsManifold planeModel ∞ M] in
lemma circularBoundaryParam_target (p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) (t : ℝ) :
    circularParam (coordinateChart p p) r t ∈ (coordinateChart p).target :=
  hreg (le_of_eq (circularParam_radius _ _ _))

lemma circularBoundaryParam_smooth (p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContMDiff 𝓘(ℝ) planeModel ∞ (circularBoundaryParam p r) := by
  intro t
  exact (((coordinateChart_symm_smoothOn p) _ (circularBoundaryParam_target p hreg t)).contMDiffAt
    ((coordinateChart p).open_target.mem_nhds (circularBoundaryParam_target p hreg t))).comp t
      ((circularParam_smooth _ r).contMDiff.contMDiffAt)

omit [IsManifold planeModel ∞ M] in
lemma circularBoundary_image (p : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularBoundary p r = circularBoundaryParam p r '' Icc (-Real.pi) Real.pi := by
  ext x
  constructor
  · rintro ⟨hxs,hx⟩
    obtain ⟨t,ht,he⟩ := circularParam_covers hr hx
    exact ⟨t,ht,by rw [circularBoundaryParam,he,(coordinateChart p).left_inv hxs]⟩
  · rintro ⟨t,ht,rfl⟩
    have htgt := circularBoundaryParam_target p hreg t
    refine ⟨(coordinateChart p).map_target htgt,?_⟩
    change circularRadiusSquared _ ((coordinateChart p) ((coordinateChart p).symm _)) = _
    rw [(coordinateChart p).right_inv htgt,circularParam_radius]

lemma circularBoundary_compact (p : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularBoundary p r) := by
  rw [circularBoundary_image p hr hreg]
  exact isCompact_Icc.image (circularBoundaryParam_smooth p hreg).continuous

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
