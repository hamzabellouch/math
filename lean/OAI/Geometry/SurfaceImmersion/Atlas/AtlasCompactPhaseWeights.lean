import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseWeights
import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseNeighborhood
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! One frequency per global phase, chosen simultaneously on every chart overlap. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial.Perturbation (modeSupport)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Compactness selects frequencies before any target tensor or correction scale.
The same frequency works in every chart that meets the phase support. -/
theorem exists_overlap_phase_weights {ι : Type*} [Finite ι]
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (hImm : ∀ k p, p ∈ tsupport (A.weight k) → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p)))
    (hgood : ∀ k a p, p ∈ tsupport (A.weight k) → p ∈ S a →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
        (coordinateChart (k : M) p))
        (phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p))) :
    ∃ w : ι → ℝ, (∀ a, 0 < w a) ∧
      ∀ k a b, a ≠ b → ∀ p, p ∈ tsupport (A.weight k) → p ∈ S a → p ∈ S b →
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
          (coordinateChart (k : M) p))
          (w a • phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) +
           w b • phaseDerivative (A.vectorPlaneRead k (φ b)) (coordinateChart (k : M) p)) ∧
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
          (coordinateChart (k : M) p))
          (w a • phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) -
           w b • phaseDerivative (A.vectorPlaneRead k (φ b)) (coordinateChart (k : M) p)) := by
  classical
  let X := Σ k : A.centers, ↥(tsupport (A.weight k))
  let : ∀ k : A.centers, CompactSpace ↥(tsupport (A.weight k)) :=
    fun k => isCompact_iff_compactSpace.mp (isClosed_tsupport (A.weight k)).isCompact
  let point : X → M := fun x => x.2.1
  have hpoint : Continuous point := continuous_sigma fun _ => continuous_subtype_val
  let B : X → Fin 3 → RVec 4 := fun x =>
    realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead x.1 F)
      (coordinateChart (x.1 : M) x.2.1)
  let ξ : ι → X → Base := fun a x =>
    phaseDerivative (A.vectorPlaneRead x.1 (φ a)) (coordinateChart (x.1 : M) x.2.1)
  have hc (k : A.centers) : Continuous
      (fun p : ↥(tsupport (A.weight k)) => coordinateChart (k : M) p.1) :=
    (coordinateChart (k : M)).continuousOn.comp_continuous continuous_subtype_val
      (fun p => by simpa only [coordinateChart_source,chart_source] using A.weight_support k p.2)
  have hB : Continuous B := by
    apply continuous_sigma
    intro k
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p : ↥(tsupport (A.weight k)) =>
      coordinateChart (k : M) p.1) ((contDiffAt_realSecondTensor
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth k hF)) _
      (gramDet_ne_zero_of_injective _ (hImm k p.1 p.2))).continuousAt) (hc k).continuousAt
  have hξ (a : ι) : Continuous (ξ a) := continuous_sigma fun k =>
    (continuous_phaseDerivative (A.vectorPlaneRead_smooth k (hφ a))).comp (hc k)
  let K : ι → ι → Set X := fun a b => point ⁻¹' (S a ∩ S b)
  have hK (a b : ι) : IsCompact (K a b) :=
    ((hS a).inter (hS b)).preimage hpoint |>.isCompact
  have hKs (a b : ι) : K a b = K b a := by simp only [K,inter_comm]
  obtain ⟨w,hw,hpairs⟩ := finite_compact_good_weights K hK hKs B ξ hB hξ
    (fun a _ _ x hx => hgood x.1 a x.2.1 x.2.2 hx.1)
  refine ⟨w,hw,?_⟩
  intro k a b hab p hp hpa hpb
  exact hpairs a b hab ⟨k,⟨p,hp⟩⟩ ⟨hpa,hpb⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
