import OAI.Geometry.SurfaceImmersion.Atlas.CenteredConvexPhase
import OAI.Geometry.SurfaceImmersion.Primitive.CurvedAtlasPrimitives

namespace OAI

/-! Concrete finite primitive data from the centered convex phases. The
coefficient maps are the actual inverses of their three gradient squares. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance centeredPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance centeredPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance centeredPrimitiveDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance centeredPrimitiveDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance centeredPrimitiveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance centeredPrimitiveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def centeredPhaseFamily (ell : A.centers → Fin 3 → SmallModes.Base)
    (L : A.centers → ℝ) (i : A.centers) (j : Fin 3) : SmallModes.Base → ℝ :=
  centeredConvexPhase (ell i j) (L i) (coordinateChart (i : M) (i : M))

def centeredAtlasBasis (P : A.centers → PhaseBasis)
    (ell : A.centers → Fin 3 → SmallModes.Base) (L : A.centers → ℝ)
    (i : A.centers) (y : JetPolynomial.Base) : PhaseBasis :=
  centeredSpatialBasis (P i) (ell i) (L i) (coordinateChart (i : M) (i : M))
    (JetPolynomial.planeCoordinateIsometry y)

variable [CompactSpace M]

/-- Fixed compact cone and connection data select the phase parameters before
the linear perturbations and target. A subordinate circular atlas then gives
actual smooth supported amplitudes and an exact global primitive sum. -/
theorem compact_centered_atlas_primitives
    (P : A.centers → PhaseBasis)
    (T : A.centers → Set PhaseMean.Tensor)
    (hT : ∀ i, IsCompact (T i))
    (hTpos : ∀ i H, H ∈ T i → ∀ j, 0 < (P i).Q j H)
    (J : A.centers → Set MetricFirstJet)
    (hJ : ∀ i, IsCompact (J i))
    (hdet : ∀ i t, t ∈ J i → metricJetDet t ≠ 0)
    (hw : ∀ i p, 0 ≤ A.weight i p)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ L r eps : A.centers → ℝ,
      (∀ i, 0 < L i ∧ 0 < r i ∧ 0 < eps i) ∧
      ∀ ell : A.centers → Fin 3 → SmallModes.Base,
        (∀ i, ‖ell i-(P i).ξ‖ < eps i) →
        (∀ i p, p ∈ tsupport (A.weight i) →
          ‖coordinateChart (i : M) p-coordinateChart (i : M) (i : M)‖ ≤ r i) →
        ∀ u : ∀ p : M, CovariantTwoTensor p,
          ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
            (fun p => TotalSpace.mk' TensorFiber p (u p)) →
          (∀ p v w, u p v w = u p w v) →
          (∀ i p, p ∈ tsupport (A.weight i) →
            A.tensorChartRead i u (chart (i : M) p) ∈ T i) →
          (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞
            (A.curvedPrimitiveAmplitude (A.centeredAtlasBasis P ell L) u a)) ∧
          (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞
            (A.curvedAtlasPhase (A.centeredPhaseFamily ell L) a)) ∧
          (∀ a, tsupport (A.curvedPrimitiveAmplitude (A.centeredAtlasBasis P ell L) u a) =
            tsupport (A.weight a.1)) ∧
          (∀ p, (∑ a : A.centers × Fin 3,
            A.curvedPrimitiveTensor (A.centeredAtlasBasis P ell L) u a p) = u p) ∧
          (∀ a p (v w : TangentSpace planeModel p),
            A.curvedPrimitiveTensor (A.centeredAtlasBasis P ell L) u a p v w =
              (A.curvedPrimitiveAmplitude (A.centeredAtlasBasis P ell L) u a p)^2 *
                (show ℝ from mfderiv planeModel 𝓘(ℝ)
                  (A.curvedAtlasPhase (A.centeredPhaseFamily ell L) a) p v) *
                (show ℝ from mfderiv planeModel 𝓘(ℝ)
                  (A.curvedAtlasPhase (A.centeredPhaseFamily ell L) a) p w)) := by
  choose L r eps hL hr heps hall using fun i =>
    compact_centered_spatial_basis (P i) (hT i) (hTpos i) (hJ i) (hdet i)
  refine ⟨L,r,eps,fun i => ⟨hL i,hr i,heps i⟩,?_⟩
  intro ell hell hsmall u hu hsymm hvalues
  have hb (i : A.centers) (p : M) (hp : p ∈ tsupport (A.weight i)) :=
    hall i (ell i) (hell i) (coordinateChart (i : M) (i : M))
      (coordinateChart (i : M) p) (hsmall i p hp)
  have hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (A.centeredAtlasBasis P ell L i (chart (i : M) p)).Q j
        (A.tensorChartRead i u (chart (i : M) p)) := by
    intro i j p hp
    exact (hb i p hp).2.1 _ (hvalues i p hp) j
  have hQ : ∀ i j p, p ∈ tsupport (A.weight i) →
      ContDiffAt ℝ ∞ (fun y => (A.centeredAtlasBasis P ell L i y).Q j)
        (chart (i : M) p) := by
    intro i j p hp
    exact ((hb i p hp).2.2.1 j).comp (chart (i : M) p)
      JetPolynomial.planeCoordinateIsometry.contDiff.contDiffAt
  have hphi : ∀ i j, ContDiff ℝ ∞ (A.centeredPhaseFamily ell L i j) :=
    fun i j => centeredConvexPhase_smooth _ _ _
  have hfit : ∀ i j p, p ∈ tsupport (A.weight i) →
      (A.centeredAtlasBasis P ell L i (chart (i : M) p)).ξ j =
        phaseDerivative (A.centeredPhaseFamily ell L i j) (coordinateChart (i : M) p) := by
    intro i j p hp
    exact congrFun (hb i p hp).1 j
  refine ⟨fun a => A.curvedPrimitiveAmplitude_smooth _ u hu hQ hpos a,
    fun a => A.curvedAtlasPhase_smooth _ hphi a,?_,
    A.sum_curvedPrimitiveTensor _ u hsymm (fun i j p hp => (hpos i j p hp).le),
    A.curvedPrimitiveTensor_apply _ u _ hphi houter hfit⟩
  intro a
  change closure (Function.support _) = closure (Function.support _)
  congr 1
  ext p
  change A.curvedPrimitiveAmplitude (A.centeredAtlasBasis P ell L) u a p ≠ 0 ↔
    A.weight a.1 p ≠ 0
  have ha := A.curvedPrimitiveAmplitude_nonneg (A.centeredAtlasBasis P ell L) u hw a p
  constructor
  · intro hn
    exact ((A.curvedPrimitiveAmplitude_pos_iff _ u hpos a p).mp
      (lt_of_le_of_ne ha (Ne.symm hn))).ne'
  · intro hn
    exact ((A.curvedPrimitiveAmplitude_pos_iff _ u hpos a p).mpr
      (lt_of_le_of_ne (hw a.1 p) (Ne.symm hn))).ne'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
