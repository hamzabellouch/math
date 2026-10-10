import OAI.Geometry.SurfaceImmersion.Geometry.ReferencePerturbationStability
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPrimitiveFamily

namespace OAI

/-! Actual positive smooth primitive decompositions of every nearby
remainder, using independently perturbed supported weights and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance referenceFamilyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceFamilyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance referenceFamilyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance referenceFamilyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance referenceFamilySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance referenceFamilySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem corrected_smooth_family {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ phaseTol weightTol mapTol : ℝ, 0 < phaseTol ∧ 0 < weightTol ∧ 0 < mapTol ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < phaseTol) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a p, 0 ≤ psi a p) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < weightTol) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mapTol (G-F) →
      ∃ f : SmoothPrimitiveFamily (d.B.centers × Fin 3) (g.inner-inducedTensor (r • G)),
        f.phase = d.perturbedPhases ell ∧
        f.amplitude = d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
          (g.inner-inducedTensor (r • G)) ∧
        (∀ a p, 0 ≤ f.amplitude a p) ∧
        (∀ a p, 0 < f.amplitude a p ↔ 0 < psi a p) ∧
        ∀ a, tsupport (f.amplitude a) ⊆ tsupport (psi a) := by
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hstable⟩ := d.circular_operator_metric_stability hF r href
  refine ⟨pt,wt,mt,hpt,hwt,hmt,?_⟩
  intro ell psi hell hpsi hnon hs hw G hG hnear
  obtain ⟨hinv,hpos⟩ := hstable ell psi hell hs hw G hG hnear
  let phi := d.perturbedPhases ell
  let u := g.inner-inducedTensor (r • G)
  have hphi (a : d.B.centers × Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (phi a) :=
    d.B.curvedAtlasPhase_smooth (d.B.centeredPhaseFamily ell d.L)
      (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) a
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
  have hp : ∀ a p, p ∈ tsupport (psi a) →
      0 < d.B.primitiveCoefficientField d.basis a p
        (d.B.correctedPrimitiveTensor d.basis psi phi u p) :=
    fun a p hp => hpos a p (hs a hp)
  let amp := d.B.correctedPrimitiveAmplitude d.basis psi phi u
  let f : SmoothPrimitiveFamily (d.B.centers × Fin 3) u := {
    amplitude := amp
    phase := phi
    smoothAmplitude := fun a => d.B.correctedPrimitiveAmplitude_smooth_of_data
      d.basis psi phi hpsi hphi (fun a => (hs a).trans (d.B.weight_support a.1))
      (fun a p ha => d.basis_smooth a.1 (hs a ha) a.2) d.outer hinv u hu hp a
    smoothPhase := hphi
    sum_eq := d.B.correctedPrimitiveAmplitude_reconstruct d.basis psi phi hinv u hsym
      (fun a p ha => (hp a p ha).le) }
  refine ⟨f,rfl,rfl,?_,?_,?_⟩
  · intro a p
    exact mul_nonneg (hnon a p) (Real.sqrt_nonneg _)
  · exact d.B.correctedPrimitiveAmplitude_pos_iff d.basis psi phi u hp
  · intro a
    exact tsupport_mul_subset_left

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
