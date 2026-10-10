import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryTangencies

namespace OAI

/-! The generic phase choice for the actual finite circular disk family.
Both finiteness of tangencies on the surface and cross-chart covector
nonparallelism follow from the preceding explicit parameter construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Countable κ]

theorem exists_generic_circular_phases
    (center : ι → M) (L r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hreg : ∀ i, circularCoordinateRegion (center i) (r i) ⊆ (coordinateChart (center i)).target)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (base point : κ → M)
    (hbase : ∀ k, point k ∈ (coordinateChart (base k)).source)
    (hfirst : ∀ k, point k ∈ (coordinateChart (center (first k))).source)
    (hsecond : ∀ k, point k ∈ (coordinateChart (center (second k))).source)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ i j, (circularPhaseTangencies (center i) (center j) (ell i) (L i) (r j) (r i)).Finite) ∧
      (∀ k, covectorDet
        (phaseDerivative (centeredAtlasPhase (center (first k)) (ell (first k)) (L (first k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k)))
        (phaseDerivative (centeredAtlasPhase (center (second k)) (ell (second k)) (L (second k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k))) ≠ 0) := by
  let K : ι × ι → Set ℝ := fun a => circularArcCompact (center a.1) (center a.2) (r a.2) (r a.1)
  let V : ι × ι → Set ℝ := fun a => circularArcDomain (center a.1) (center a.2) (r a.2)
  let u : ι × ι → ℝ → CurvePlane := fun a => circularArc (center a.1) (center a.2) (r a.2)
  have hK (a : ι × ι) : IsCompact (K a) := circularArcCompact_compact _ _ (hreg a.2) (hreg a.1)
  have hV (a : ι × ι) : IsOpen (V a) := circularArcDomain_open _ _ (hreg a.2)
  have hu (a : ι × ι) : ContDiffOn ℝ ∞ (u a) (V a) := circularArc_smooth _ _ (hreg a.2)
  have hKV (a : ι × ι) : K a ⊆ V a := circularArcCompact_subset _ _ (hreg a.1)
  have hv (a : ι × ι) (t : ℝ) (ht : t ∈ K a) : deriv (u a) t ≠ 0 :=
    circularArc_regular _ _ (hr a.2) (hreg a.2) (hKV a ht)
  obtain ⟨ell,hell,hfinite,_,hcross⟩ := exists_generic_atlas_phases_on center L Prod.fst
    u V hV hu K hK hKV hv first second hdistinct base point hbase hfirst hsecond U hU hne
  refine ⟨ell,hell,?_,hcross⟩
  intro i j
  exact circularPhaseTangencies_finite (center i) (center j) (ell i) (L i)
    (hr j) (hreg j) (hreg i) (hfinite (i,j))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
