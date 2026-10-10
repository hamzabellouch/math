import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCoordinateCovector
import OAI.Geometry.SurfaceImmersion.Correction.TensorOperatorSmooth

namespace OAI

/-! Identification of a supported analytic primitive with the square of its
actual global surface phase differential. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates PhaseGeometry
local instance globalPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance globalPrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance globalPrimitiveDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance globalPrimitiveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalPrimitiveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma localized_primitive_tensor_at (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (χ : JetPolynomial.Base → ℝ) (a : SmallModes.Base → ℝ)
    {phi : M → ℝ} {p : M} (hp : p ∈ (chart (i : M)).source)
    (hphi : phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0)) :
    A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)) p =
      (A.outer i p * χ (chart (i : M) p) * (a (surfacePhaseChart (i : M) e p))^2) •
        phaseDifferentialSquare phi p := by
  ext v w
  rw [A.tensorRestore_apply i _ hp,localizedTensorPullback_first_square,map_smul]
  simp only [smul_apply,smul_eq_mul,fiberFromThree_apply,covectorSquare_evaluate]
  rw [← A.phaseFirst_mfderiv i e he hp hphi v,← A.phaseFirst_mfderiv i e he hp hphi w]
  let dv : ℝ := mfderiv planeModel 𝓘(ℝ) phi p v
  let dw : ℝ := mfderiv planeModel 𝓘(ℝ) phi p w
  change A.outer i p * (χ (chart (i : M) p) * (a (baseEquiv (e (chart (i : M) p))))^2 *
    (dv * dw)) =
    (A.outer i p * χ (chart (i : M) p) * (a (baseEquiv (e (chart (i : M) p))))^2) *
      (dv * dw)
  ring

theorem phase_primitive_global_tensor (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) {χ : JetPolynomial.Base → ℝ}
    (hχs : tsupport χ ⊆ e.source) {a : SmallModes.Base → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) {D : Set M}
    (hDs : D ⊆ (surfacePhaseChart (i : M) e).source)
    (hapos : ∀ x, 0 < a x ↔ x ∈ (surfacePhaseChart (i : M) e) '' D)
    {f phi : M → ℝ}
    (haf : ∀ p ∈ D, a (surfacePhaseChart (i : M) e p) = f p)
    (hfzero : ∀ p ∉ D, f p = 0)
    (houter : ∀ p ∈ D, A.outer i p = 1)
    (hone : ∀ p ∈ D, χ (chart (i : M) p) = 1)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0)) :
    A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)) =
      fun p => (f p)^2 • phaseDifferentialSquare phi p := by
  funext p
  by_cases hpD : p ∈ D
  · rw [A.localized_primitive_tensor_at i e he χ a (hDs hpD).1 (hphi p hpD),
      houter p hpD,hone p hpD,haf p hpD,one_mul,one_mul]
  rw [hfzero p hpD,zero_pow (by decide : 2 ≠ 0),zero_smul]
  by_cases hp : p ∈ (chart (i : M)).source
  · have hzero : localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0])
        (chart (i : M) p) = 0 := by
      by_cases hχ : χ (chart (i : M) p) = 0
      · simp only [localizedTensorPullback,hχ,zero_smul]
      have hep : p ∈ (surfacePhaseChart (i : M) e).source :=
        ⟨hp,hχs (subset_tsupport χ hχ)⟩
      have ha : a (surfacePhaseChart (i : M) e p) = 0 := by
        apply le_antisymm _ (ha0 _)
        apply le_of_not_gt
        intro hpos
        obtain ⟨q,hq,heq⟩ := (hapos _).mp hpos
        have hqp : q = p := (surfacePhaseChart (i : M) e).injOn (hDs hq) hep heq
        exact hpD (hqp ▸ hq)
      rw [localizedTensorPullback_first_square]
      change (χ (chart (i : M) p) * (a (surfacePhaseChart (i : M) e p))^2) • _ = 0
      rw [ha,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_smul]
    ext v w
    rw [A.tensorRestore_apply i _ hp,hzero,map_zero]
    simp
  · have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [bundleRestore,ho,zero_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
