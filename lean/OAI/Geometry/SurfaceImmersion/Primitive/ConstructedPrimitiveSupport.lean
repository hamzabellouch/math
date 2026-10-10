import OAI.Geometry.SurfaceImmersion.Primitive.CompactPrimitiveSupport
import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseAmplitude
import OAI.Geometry.SurfaceImmersion.Primitive.PhasePrimitiveGlobalTensor

namespace OAI

/-! Construct the smooth amplitude and the exact localized tensor of an
actual surface primitive, retaining its precise geometric support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates PhaseGeometry
local instance constructedSupportFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance constructedSupportFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance constructedSupportDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance constructedSupportDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance constructedSupportSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance constructedSupportSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem constructed_primitive_support (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hDs : closure D ⊆ (surfacePhaseChart (i : M) e).source)
    (hactive : ∀ p ∈ closure D, A.weight i p ≠ 0)
    {f phi : M → ℝ} (hf : ContMDiff planeModel 𝓘(ℝ) ∞ f)
    (hf0 : ∀ p, 0 ≤ f p) (hfpos : ∀ p, 0 < f p ↔ p ∈ D)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0)) :
    ∃ K : Set JetPolynomial.Base, IsCompact K ∧ K ⊆ e.target ∧
      A.phaseSurfaceSupport i e K = closure D ∧
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) ∧
      (∀ p ∈ closure D, e (chart (i : M) p) ∈ K) ∧
      (∀ y ∈ K, A.chartWeight i (e.symm y) ≠ 0) ∧
      ∃ χ : JetPolynomial.Base → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ e.source ∧ (∀ x ∈ e.symm '' K, χ x = 1) ∧
      ∃ a : SmallModes.Base → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 ≤ a x) ∧
        (∀ p ∈ (surfacePhaseChart (i : M) e).source, a (surfacePhaseChart (i : M) e p) = f p) ∧
        (∀ x, 0 < a x ↔ x ∈ (surfacePhaseChart (i : M) e) '' D) ∧
        (∀ x ∉ K, a (baseEquiv x) = 0) ∧
        A.bundleRestore A.tensorTriv i
          (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)) =
          fun p => (f p)^2 • phaseDifferentialSquare phi p := by
  have hDc : IsCompact (closure D) := isClosed_closure.isCompact
  obtain ⟨K,hK,hKt,hSupport,hKA,hDK,hactiveK,χ,hχ,hχc,hχs,hχone⟩ :=
    A.compact_primitive_support i e he hDc hDs hactive
  obtain ⟨a,ha,ha0,haf,hapos,_haoff⟩ := surface_phase_amplitude (i : M) e hi hDc hDs hf hf0 hfpos
  have hfzero (p : M) (hp : p ∉ D) : f p = 0 :=
    le_antisymm (le_of_not_gt (fun hh => hp ((hfpos p).mp hh))) (hf0 p)
  have hχD (p : M) (hp : p ∈ D) : χ (chart (i : M) p) = 1 := by
    have hpe : chart (i : M) p ∈ e.source := (hDs (subset_closure hp)).2
    apply hχone
    exact ⟨e (chart (i : M) p),hDK p (subset_closure hp),e.left_inv hpe⟩
  have hzero (x : JetPolynomial.Base) (hx : x ∉ K) : a (baseEquiv x) = 0 := by
    apply le_antisymm _ (ha0 _)
    apply le_of_not_gt
    intro hpos
    obtain ⟨p,hp,heq⟩ := (hapos _).mp hpos
    apply hx
    have heqx := congrArg baseEquiv.symm heq
    change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) = baseEquiv.symm (baseEquiv x) at heqx
    have hh : e (chart (i : M) p) = x := by
      simpa only [baseEquiv.symm_apply_apply] using heqx
    exact hh ▸ hDK p (subset_closure hp)
  refine ⟨K,hK,hKt,hSupport,hKA,hDK,hactiveK,χ,hχ,hχc,hχs,hχone,a,ha,ha0,haf,hapos,hzero,?_⟩
  exact A.phase_primitive_global_tensor i e he hχs ha0
    (fun _ hp => hDs (subset_closure hp)) hapos (fun p hp => haf p (hDs (subset_closure hp)))
    hfzero (fun p hp => A.outer_one i p (subset_tsupport _ (hactive p (subset_closure hp)))) hχD hphi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
