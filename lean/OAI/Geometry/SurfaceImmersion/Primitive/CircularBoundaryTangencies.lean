import OAI.Geometry.SurfaceImmersion.Whitney.CircularBoundaryArcs
import OAI.Geometry.SurfaceImmersion.Atlas.LocalGenericAtlasPhases

namespace OAI

/-! Derivatives along the explicit circle equal evaluation of the actual
phase covector on its nonzero angular tangent. Compact parameter finiteness
therefore gives finiteness of the genuine surface tangency set. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularAngularTangent (c x : CurvePlane) : CurvePlane := (-(x.2-c.2),x.1-c.1)

lemma circularAngularTangent_param (c : CurvePlane) (r t : ℝ) :
    circularAngularTangent c (circularParam c r t) = circularVelocity r t := by
  ext <;> dsimp [circularAngularTangent,circularParam,circularVelocity] <;> ring

def circularPhaseDerivative (q p : M) (ell : CurvePlane) (L : ℝ) (x : M) : ℝ :=
  phaseLinear (phaseDerivative (centeredAtlasPhase q ell L ∘ (coordinateChart p).symm)
    (coordinateChart p x))
    (circularAngularTangent (coordinateChart p p) (coordinateChart p x))

lemma circularPhaseDerivative_eq_deriv (q p : M) (ell : CurvePlane) (L : ℝ) {r t : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (ht : t ∈ circularArcDomain q p r) :
    circularPhaseDerivative q p ell L (circularBoundaryParam p r t) =
      deriv (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) t := by
  let x := circularParam (coordinateChart p p) r t
  let f : CurvePlane → ℝ := centeredAtlasPhase q ell L ∘ (coordinateChart p).symm
  have hx : x ∈ (coordinateTransition q p).source := ⟨circularBoundaryParam_target p hreg t,ht⟩
  have hf : DifferentiableAt ℝ f x :=
    ((centeredConvexPhase_smooth ell L (coordinateChart q q)).differentiable (by simp) _).comp x
      ((((coordinateTransition_smoothOn q p) x hx).contDiffAt
        ((coordinateTransition q p).open_source.mem_nhds hx)).differentiableAt (by simp))
  have hd := hf.hasFDerivAt.comp_hasDerivAt t (circularParam_hasDerivAt (coordinateChart p p) r t)
  have he : (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) =
      f ∘ circularParam (coordinateChart p p) r := rfl
  rw [he,hd.deriv]
  unfold circularPhaseDerivative
  simp only [circularBoundaryParam]
  rw [(coordinateChart p).right_inv (circularBoundaryParam_target p hreg t),
    circularAngularTangent_param,phaseLinear_phaseDerivative]

def circularPhaseTangencies (q p : M) (ell : CurvePlane) (L r R : ℝ) : Set M :=
  circularBoundary p r ∩ circularDiskClosure q R ∩ {x | circularPhaseDerivative q p ell L x = 0}

lemma circularPhaseTangencies_finite (q p : M) (ell : CurvePlane) (L : ℝ) {r R : ℝ}
    (hr : 0 < r) (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target)
    (hfinite : (circularArcCompact q p r R ∩ {t |
      deriv (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) t = 0}).Finite) :
    (circularPhaseTangencies q p ell L r R).Finite := by
  apply (hfinite.image (circularBoundaryParam p r)).subset
  rintro x ⟨⟨hx,hQx⟩,hzero⟩
  obtain ⟨t,ht,rfl⟩ := circularArcCompact_covers q p hr hreg ⟨hx,hQx⟩
  refine ⟨t,⟨ht,?_⟩,rfl⟩
  change deriv (fun s => centeredAtlasPhase q ell L (circularBoundaryParam p r s)) t = 0
  rw [← circularPhaseDerivative_eq_deriv q p ell L hreg
    (circularArcCompact_subset q p hQ ht)]
  exact hzero

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
