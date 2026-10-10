import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceAmplitudeParameterBounds
import OAI.Geometry.SurfaceImmersion.Atlas.ReferencePhaseC1
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateDerivative
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAmplitudeZero
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateC1Bounds

namespace OAI

/-! Uniform first-derivative bounds for the genuine corrected amplitudes.
The tolerances and bounds precede all later finite cycles and boundary choices. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance actualC1FiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualC1FiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance actualC1FiberAdd : AddCommGroup TensorFiber := actualC1FiberNormed.toAddCommGroup
local instance actualC1TensorDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1TensorDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1FiberT2 : T2Space TensorFiber := inferInstance
local instance actualC1TensorDualT2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorT2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1DataNormed (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataSpace (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataT2 (ι : Type*) [Fintype ι] : T2Space (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataDualNormed (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1DataDualSpace (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance actualC1DualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualC1DualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualC1SectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualC1SectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem uniform_actual_amplitude_C1 {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ pt wt mt : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧
      ∀ Dw Du : ℝ, 0 ≤ Dw → 0 ≤ Du → ∃ E : ℝ, 1 ≤ E ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      (∀ a, d.B.WeightedBound 1 1 Dw (psi a)) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) →
      d.B.TensorWeightedBound 1 1 Du (g.inner-inducedTensor (r • G)) →
      ∀ i a p, p ∈ tsupport (d.B.weight i) →
      let amp := d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) a
      |amp p| ≤ E ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ E := by
  obtain ⟨pt,wt,mt,R,hpt,hwt,hmt,hR,hparam⟩ := d.actual_amplitude_parameter_bound hF r href
  refine ⟨min pt 1,wt,mt,lt_min hpt zero_lt_one,hwt,hmt,?_⟩
  intro Dw Du hDw hDu
  obtain ⟨Dq,hDq,hq⟩ := d.B.coefficientFrameRead_C1_bound d.basis
    (fun a _p hp => d.basis_smooth a.1 hp a.2)
  obtain ⟨W,hW,hw⟩ := d.B.coordinate_C1_bound (V := ℝ) hDw
  obtain ⟨V,hV,hv⟩ := d.perturbed_phase_C1_bound
  obtain ⟨H,hH,hHbound⟩ := d.B.tensorFrameRead_C1_bound hDu
  let D := Dq+W+V+H
  have hD : 0 ≤ D := by dsimp only [D]; linarith
  have hqD : Dq ≤ D := by dsimp only [D]; linarith
  have hWD : W ≤ D := by dsimp only [D]; linarith
  have hVD : V ≤ D := by dsimp only [D]; linarith
  have hHD : H ≤ D := by dsimp only [D]; linarith
  let E := R*(1+D)
  have hRE : R ≤ E := by dsimp only [E]; nlinarith
  have hDE : R*D ≤ E := by dsimp only [E]; nlinarith
  refine ⟨E,hR.trans hRE,?_⟩
  intro ell psi hell hpsi hs hclose hbpsi G hG hnear hbu i a p hp
  let u := g.inner-inducedTensor (r • G)
  let phi := d.perturbedPhases ell
  have hphi (b : d.B.centers × Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (phi b) :=
    d.B.curvedAtlasPhase_smooth (d.B.centeredPhaseFamily ell d.L)
      (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) b
  have hscaled : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)) :=
    g.contMDiff.sub_section (A.inducedTensor_smooth hscaled)
  have hsym : ∀ p v w, u p v w = u p w v := by
    intro p v w
    change g.inner p v w-inner ℝ (mfderiv planeModel spaceModel (r • G) p v)
      (mfderiv planeModel spaceModel (r • G) p w) =
      g.inner p w v-inner ℝ (mfderiv planeModel spaceModel (r • G) p w)
      (mfderiv planeModel spaceModel (r • G) p v)
    rw [g.symm,real_inner_comm]
  have hell1 : ∀ i j, ‖ell i j-(d.P i).ξ j‖ ≤ 1 :=
    fun i j => (hell i j).le.trans (min_le_right _ _)
  by_cases ha : p ∈ tsupport (d.B.weight a.1)
  · have hd : ‖fderiv ℝ (d.B.primitiveCoordinateData d.basis psi phi u i
        {b | p ∈ tsupport (d.B.weight b.1)}) (chart (i : M) p)‖ ≤ D := by
      apply d.B.primitiveCoordinateData_fderiv_bound d.basis psi phi hpsi hphi
        (fun b _p hb => d.basis_smooth b.1 hb b.2) u hu i hp hD
      · intro b hb
        exact (hq i b p hp hb).2.trans hqD
      · intro b
        exact (hw (psi b) (hpsi b) (hbpsi b) i p hp).2.trans hWD
      · intro b _hb
        exact (hv ell hell1 i b p hp).2.trans hVD
      · exact (hHbound u hu hsym hbu i p hp).2.trans hHD
    have hpa := hparam ell psi (fun i j => (hell i j).trans_le (min_le_left _ _))
      hclose G hG hnear i p hp a ha
    have hh := d.B.correctedAmplitude_coordinate_bound d.basis psi phi hpsi hphi
      (fun b _p hb => d.basis_smooth b.1 hb b.2) hs u hu i hp a ha R D hd hpa
    exact ⟨hh.1.trans hRE,hh.2.trans hDE⟩
  · have hz := d.B.correctedAmplitude_zero_coordinate d.basis psi phi u hs i a
      (d.B.weight_support i hp) ha
    change |d.B.correctedPrimitiveAmplitude d.basis psi phi u a p| ≤ E ∧ _
    rw [hz.1,hz.2,abs_zero,norm_zero]
    exact ⟨zero_le_one.trans (hR.trans hRE),zero_le_one.trans (hR.trans hRE)⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
