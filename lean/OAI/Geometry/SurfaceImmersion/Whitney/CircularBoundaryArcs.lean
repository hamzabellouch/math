import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryParam

namespace OAI

/-! Compact boundary portions in another phase chart have actual smooth
regular coordinate arcs, extended later only for parameter selection. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

lemma coordinateTransition_derivative_injective (q p : M) {x : CurvePlane}
    (hx : x ∈ (coordinateTransition q p).source) :
    Function.Injective (fderiv ℝ (coordinateTransition q p) x) := by
  let e := coordinateTransition q p
  have hd := (((coordinateTransition_smoothOn q p) x hx).contDiffAt
    (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hi := (((coordinateTransition_symm_smoothOn q p) (e x) (e.map_source hx)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  have he : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hc : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ CurvePlane := by
    rw [← fderiv_comp x hi hd,he.fderiv_eq,fderiv_id]
  intro v w hvw
  have hh := congrArg (fderiv ℝ e.symm (e x)) hvw
  change ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) v =
    ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) w at hh
  simpa only [hc,ContinuousLinearMap.id_apply] using hh

end ClosedSurfaceR4.PhaseGeometry
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularArcDomain (q p : M) (r : ℝ) : Set ℝ :=
  circularBoundaryParam p r ⁻¹' (coordinateChart q).source

def circularArc (q p : M) (r : ℝ) : ℝ → CurvePlane :=
  coordinateChart q ∘ circularBoundaryParam p r

lemma circularArcDomain_open (q p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsOpen (circularArcDomain q p r) :=
  (coordinateChart q).open_source.preimage (circularBoundaryParam_smooth p hreg).continuous

lemma circularArc_smooth (q p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContDiffOn ℝ ∞ (circularArc q p r) (circularArcDomain q p r) := by
  exact ((coordinateChart_smoothOn q).comp
    (circularBoundaryParam_smooth p hreg).contMDiffOn (fun _ ht => ht)).contDiffOn

lemma circularArc_regular (q p : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    {t : ℝ} (ht : t ∈ circularArcDomain q p r) : deriv (circularArc q p r) t ≠ 0 := by
  let x := circularParam (coordinateChart p p) r t
  have hx : x ∈ (coordinateTransition q p).source := ⟨circularBoundaryParam_target p hreg t,ht⟩
  have hd := ((((coordinateTransition_smoothOn q p) x hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hcurve := hd.comp_hasDerivAt t (circularParam_hasDerivAt (coordinateChart p p) r t)
  have he : circularArc q p r = coordinateTransition q p ∘ circularParam (coordinateChart p p) r := rfl
  rw [he,hcurve.deriv]
  intro hz
  have hinj := coordinateTransition_derivative_injective q p hx
  apply circularVelocity_ne_zero hr.ne' t
  apply hinj
  simpa only [map_zero] using hz

variable [T2Space M]

def circularArcCompact (q p : M) (r R : ℝ) : Set ℝ :=
  Icc (-Real.pi) Real.pi ∩ circularBoundaryParam p r ⁻¹' circularDiskClosure q R

lemma circularArcCompact_compact (q p : M) {r R : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target) :
    IsCompact (circularArcCompact q p r R) :=
  isCompact_Icc.inter_right ((circularDiskClosure_compact q R hQ).isClosed.preimage
    (circularBoundaryParam_smooth p hreg).continuous)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularArcCompact_subset (q p : M) {r R : ℝ}
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target) :
    circularArcCompact q p r R ⊆ circularArcDomain q p r := by
  intro t ht
  exact circularDiskClosure_source q R hQ ht.2

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularArcCompact_covers (q p : M) {r R : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    {x : M} (hx : x ∈ circularBoundary p r ∩ circularDiskClosure q R) :
    ∃ t ∈ circularArcCompact q p r R, circularBoundaryParam p r t = x := by
  rw [circularBoundary_image p hr hreg] at hx
  obtain ⟨t,ht,he⟩ := hx.1
  exact ⟨t,⟨ht,by simpa only [mem_preimage,he] using hx.2⟩,he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
