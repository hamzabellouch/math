import OAI.Geometry.SurfaceImmersion.Atlas.OuterChartDifferential
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential
import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormalGluing

namespace OAI

/-! A normal vector in the nonlinear phase coordinates is normal to the
actual immersion on the corresponding atlas support. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phase_chart_normal_at_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : M} (hp : p ∈ tsupport (A.weight i))
    (hx : chart (i : M) p ∈ e.source) (n : NormalFrame.Vec)
    (hn : ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p))) ⬝ᵥ n = 0)
    (v : TangentSpace planeModel p) :
    inner ℝ (surfaceDifferential F p v) (spaceCoordinates.symm n) = 0 := by
  let x := chart (i : M) p
  let H : JetPolynomial.Base → JetPolynomial.Space :=
    (spaceCoordinates ∘ A.vectorChartRead i F) ∘ e.symm
  have hH : ContDiff ℝ ∞ H :=
    (spaceCoordinates.contDiff.comp (A.vectorChartRead_smooth i hF)).comp hi
  have hHnormal (u : JetPolynomial.Base) : fderiv ℝ H (e x) u ⬝ᵥ n = 0 := by
    have hh := hn (baseEquiv u)
    change fderiv ℝ (H ∘ baseEquiv.symm) (baseEquiv (e x)) (baseEquiv u) ⬝ᵥ n = 0 at hh
    rw [fderiv_comp _ (hH.differentiable (by simp) _) baseEquiv.symm.differentiableAt,
      baseEquiv.symm.fderiv,ContinuousLinearMap.comp_apply] at hh
    simpa only [baseEquiv.symm_apply_apply,ContinuousLinearEquiv.coe_coe] using hh
  have hrel : H ∘ e =ᶠ[𝓝 x] spaceCoordinates ∘ A.vectorChartRead i F := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [H,Function.comp_apply,e.left_inv hy]
  have hd := hrel.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x (hH.differentiable (by simp) _) (he.differentiable (by simp) _)] at hd
  have hd' := fderiv_comp x spaceCoordinates.differentiableAt
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) _)
  rw [spaceCoordinates.fderiv] at hd'
  have hnormal (u : JetPolynomial.Base) :
      spaceCoordinates (fderiv ℝ (A.vectorChartRead i F) x u) ⬝ᵥ n = 0 := by
    have hh := hHnormal (fderiv ℝ e x u)
    have hh' := congrArg (fun L : JetPolynomial.Base →L[ℝ] JetPolynomial.Space => L u) hd
    rw [hd'] at hh'
    change fderiv ℝ H (e x) (fderiv ℝ e x u) =
      spaceCoordinates (fderiv ℝ (A.vectorChartRead i F) x u) at hh'
    rw [← hh']
    exact hh
  rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply,
    A.vectorChartRead_differential i hF hp]
  exact hnormal (surfaceDifferential (chart (i : M)) p v)

lemma phase_chart_normal_of_outer (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (houter : A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ))
    (hx : chart (i : M) p ∈ e.source) (n : NormalFrame.Vec)
    (hn : ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p))) ⬝ᵥ n = 0)
    (v : TangentSpace planeModel p) :
    inner ℝ (surfaceDifferential F p v) (spaceCoordinates.symm n) = 0 := by
  let x := chart (i : M) p
  let H : JetPolynomial.Base → JetPolynomial.Space :=
    (spaceCoordinates ∘ A.vectorChartRead i F) ∘ e.symm
  have hH : ContDiff ℝ ∞ H :=
    (spaceCoordinates.contDiff.comp (A.vectorChartRead_smooth i hF)).comp hi
  have hHnormal (u : JetPolynomial.Base) : fderiv ℝ H (e x) u ⬝ᵥ n = 0 := by
    have hh := hn (baseEquiv u)
    change fderiv ℝ (H ∘ baseEquiv.symm) (baseEquiv (e x)) (baseEquiv u) ⬝ᵥ n = 0 at hh
    rw [fderiv_comp _ (hH.differentiable (by simp) _) baseEquiv.symm.differentiableAt,
      baseEquiv.symm.fderiv,ContinuousLinearMap.comp_apply] at hh
    simpa only [baseEquiv.symm_apply_apply,ContinuousLinearEquiv.coe_coe] using hh
  have hrel : H ∘ e =ᶠ[𝓝 x] spaceCoordinates ∘ A.vectorChartRead i F := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [H,Function.comp_apply,e.left_inv hy]
  have hd := hrel.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x (hH.differentiable (by simp) _) (he.differentiable (by simp) _)] at hd
  have hd' := fderiv_comp x spaceCoordinates.differentiableAt
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) _)
  rw [spaceCoordinates.fderiv] at hd'
  have hnormal (u : JetPolynomial.Base) :
      spaceCoordinates (fderiv ℝ (A.vectorChartRead i F) x u) ⬝ᵥ n = 0 := by
    have hh := hHnormal (fderiv ℝ e x u)
    have hh' := congrArg (fun L : JetPolynomial.Base →L[ℝ] JetPolynomial.Space => L u) hd
    rw [hd'] at hh'
    change fderiv ℝ H (e x) (fderiv ℝ e x u) =
      spaceCoordinates (fderiv ℝ (A.vectorChartRead i F) x u) at hh'
    rw [← hh']
    exact hh
  rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply,
    A.vectorChartRead_differential_of_outer i hF hp houter]
  exact hnormal (surfaceDifferential (chart (i : M)) p v)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
