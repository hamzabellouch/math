import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Primitive.IndependentConstructedCircular

namespace OAI

/-! The constructed local primitive data feed the exact analytic theorem,
with the global rank-one metric written in the original surface variables. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
local instance patchRealizeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance patchRealizeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance patchRealizeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance patchRealizeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance patchRealizeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchRealizeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SupportedPrimitivePatch
variable {A : SmoothingAtlas M} {i : A.centers}
    {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
    {F : M → Space} {amp phi : M → ℝ} {D : Set M}

theorem exact_metric (d : SupportedPrimitivePatch A i e F amp phi D)
    {g : SmoothMetric M} (data : MetricGoodPhaseData g F)
    (hF : IsSmoothIsometricImmersion M g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  have hmetric : g.inner = inducedTensor F := by
    funext p
    ext v w
    exact (hF.2 p v w).symm
  have htarget' : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e d.cutoff
        (fun q => ![(d.amplitude (baseEquiv q))^2,0,0]) y)) := by
    rw [d.tensor]
    exact htarget
  have hCS : d.compactSet ⊆ (d.window : Set JetPolynomial.Base) ∩ e.target :=
    fun _ hx => ⟨d.support_window hx,d.target hx⟩
  let ell : JetPolynomial.Base →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hell₀ : ell (coordinateVector 0) = 1 := by simp [ell,coordinateVector]
  have hell₁ : ell (coordinateVector 1) = 0 := by simp [ell,coordinateVector]
  obtain ⟨z,hz,hz1,hzle,W,hW,hgood,_⟩ :=
    data.independent_constructed_circular_primitive_boundary A d.outer hF.1 hmetric
      i e d.phase_smooth d.inverse_smooth d.cutoff_smooth d.cutoff_compact d.cutoff_source d.cover
      d.amplitude_smooth d.region_compact d.open_region d.region_open d.normal_smooth
      d.immersion d.normal_properties d.convexity (fun p _ => d.amplitude_nonneg p) d.boundary
      (Curves := fun _ : Fin 0 => (∅ : Set SmallModes.Base))
      (fun _ => isCompact_empty) (fun _ => empty_subset _) (P := ∅) finite_empty
      (by simp) (E := ∅) finite_empty (empty_subset _) (by simp)
      0 le_rfl (b := fun _ : Fin 0 => fun _ => 0) (c := fun _ : Fin 0 => fun _ => 0)
      (k := fun _ : Fin 0 => fun _ => 0)
      (fun _ => contDiff_const) (fun _ => contDiff_const) (fun _ => contDiff_const)
      (fun j => Fin.elim0 j) 0 le_rfl (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      d.window d.window_compact d.phase_window d.window_region d.compactSet d.compact
      d.support_window d.inverse_support d.cutoff_one d.amplitude_off ell hell₀ hell₁ h htarget'
      d.compact hCS (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (by simp) (by simp) (by simp) 1 zero_lt_one 1 zero_lt_one
  exact ⟨W,hW,hgood⟩

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
