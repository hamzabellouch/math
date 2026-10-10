import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceAmplitudeMargin
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateTolerance
import OAI.Geometry.SurfaceImmersion.Geometry.ReferencePerturbationStability

namespace OAI

/-! The actual independent circular data remain inside the fixed positive
amplitude neighborhood for every sufficiently close starting map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance actualParamFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualParamFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance actualParamDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualParamDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualParamSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualParamSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem actual_amplitude_parameter_bound {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ pt wt mt R : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧ 1 ≤ R ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) →
      ∀ i p, p ∈ tsupport (d.B.weight i) → ∀ a : d.B.centers × Fin 3,
      p ∈ tsupport (d.B.weight a.1) →
      let z := d.B.primitiveCoordinateData d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) i {b | p ∈ tsupport (d.B.weight b.1)} (chart (i : M) p)
      (primitiveDataOperator z.1).IsInvertible ∧ 0 < primitiveParameterCoefficient a z ∧
        |primitiveParameterAmplitude a z| ≤ R ∧
        ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R := by
  obtain ⟨eps,R,heps,hR,hmargin⟩ := d.amplitude_parameter_margin
  obtain ⟨D,hD,hphase⟩ := d.B.circularPhase_frame_bound
  obtain ⟨mt,hmt,hmetric⟩ := d.metric_frame_tolerance hF r href heps
  have hDp : 0 < D+1 := by linarith
  refine ⟨eps/(D+1),eps,mt,R,div_pos heps hDp,heps,hmt,hR,?_⟩
  intro ell psi hell hw G hG hnear i p hp a ha
  apply hmargin i p hp a ha
  apply d.B.primitiveCoordinateData_sub_lt d.basis psi (fun b => d.B.weight b.1)
    (d.perturbedPhases ell) d.globalPhases (g.inner-inducedTensor (r • G)) gref.inner i
    {b | p ∈ tsupport (d.B.weight b.1)} (d.B.weight_support i hp) heps (fun b => hw b p)
  · intro b _hb
    have hs := d.B.weight_support i hp
    have he := (d.B.covectorFrame_mfderiv (d.B.circularPhase b.1 (ell b.1 b.2) (d.L b.1))
      (d.B.circularPhase_smooth _ _ _) i hs)
    have he0 := (d.B.covectorFrame_mfderiv (d.B.circularPhase b.1 ((d.P b.1).ξ b.2) (d.L b.1))
      (d.B.circularPhase_smooth _ _ _) i hs)
    change ‖d.B.phaseCovectorRead i (d.B.circularPhase b.1 (ell b.1 b.2) (d.L b.1)) (chart (i : M) p)-
      d.B.phaseCovectorRead i (d.B.circularPhase b.1 ((d.P b.1).ξ b.2) (d.L b.1)) (chart (i : M) p)‖ < eps
    simp only [SmoothingAtlas.phaseCovectorRead]
    rw [← he,← he0]
    have hb := hphase b.1 i p hp (ell b.1 b.2) ((d.P b.1).ξ b.2) (d.L b.1)
    have ht := (lt_div_iff₀ hDp).mp (hell b.1 b.2)
    have hn := norm_nonneg (ell b.1 b.2-(d.P b.1).ξ b.2)
    exact hb.trans_lt (by nlinarith)
  · have h := hmetric G hG hnear i p hp
    rw [d.B.tensor_frame_read i gref.inner gref.symm hp]
    exact h

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
