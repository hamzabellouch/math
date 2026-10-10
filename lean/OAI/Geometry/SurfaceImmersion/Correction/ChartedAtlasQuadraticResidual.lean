import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasMeanIdentity

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance quadraticAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance quadraticAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance quadraticAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance quadraticAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance quadraticAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance quadraticAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

theorem charted_family_atlas_mean_identity
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ x v v', u x v v' = u x v' v)
    (hball : ∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) =
      δ^2 • (u + A.atlasMean (fun i => (d i).mean hρ δ q) u) :=
  A.charted_atlas_mean_identity (fun i => (d i).data) hρ Q w hw hphase hcutoff hform hsupport
    u hu hsym hball hδ hτ q

theorem charted_family_atlas_quadratic_residual
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source)
    (u H : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H x)))
    (hsym : ∀ x v v', u x v v' = u x v' v)
    (hball : ∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hτ : τ ≠ 0)
    (q : ℕ)
    (hb : A.TensorWeightedBound s m C
      (u + A.atlasMean (fun i => (d i).mean hρ δ q) u - H)) :
    A.TensorWeightedBound s m (δ^2*C)
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
  have hm : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasMean (fun i => (d i).mean hρ δ q) u x)) :=
    A.tensorPlaneRestore_smooth (fun i => (d i).mean_smooth hρ δ q _)
  have hr := (hu.add_section hm).sub_section hH
  rw [A.charted_family_atlas_mean_identity d hρ Q w hw hphase hcutoff hform hsupport
    u hu hsym hball hδ hτ q, ← smul_sub]
  have hh := A.tensorWeightedBound_const_smul hr hb (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
