import OAI.Geometry.SurfaceImmersion.Atlas.ChartedPartitionLeading
import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMean
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneWeight

namespace OAI

/-! The actual quadratic zero-phase terms of the charted free oscillations
restore to the input global tensor plus the global nonlinear mean. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance chartedAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance chartedAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance chartedAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance chartedAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance chartedAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartedAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem charted_atlas_mean_identity
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : A.centers → Base → JetPolynomial.Space}
    {hG : ∀ i, ContDiff ℝ ∞ (G i)} {φ : A.centers → Fin 3 → Base → ℝ}
    {K : A.centers → Fin 3 → TopologicalSpace.Compacts Base}
    {c : ∀ i j, PolynomialSolveData (P i) ε (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase (φ i j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ (c i j).e.source →
      (d i j).cutoff ((c i j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ (c i j).e.source → (d i j).form ((c i j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ (c i j).e.source)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    A.tensorPlaneRestore (fun i => combinedQuadraticMean (P i) ε (G i) (φ i)
      (fun j => (d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) τ 0) =
        δ^2 • (u + A.atlasMean (fun i => chartedFamilyMean (n := n i) (ι := Fin 3) (P := P i) (ε := ε) (τ := τ) (s := s) (G := G i) (hG := hG i) (φ := φ i) (K := K i) (c := c i) (r := r i) (ρ := ρ) (R := R) (reference := reference i) (d i) hρ δ q) u) := by
  have hleading (i : A.centers) :
      chartedFamilyLeading (n := n i) (ι := Fin 3) (P := P i) (ε := ε) (τ := τ) (s := s) (G := G i) (hG := hG i) (φ := φ i) (K := K i) (c := c i) (r := r i) (ρ := ρ) (R := R) (reference := reference i) (d i) hρ (A.tensorPlaneRead i u) = A.tensorPlaneEncode u i := by
    rw [charted_partition_leading (d i) hρ (A.planeWeight i) (Q i) (w i)
      (hw i) (hphase i) (hcutoff i) (hform i) (hsupport i)
      (A.tensorPlaneRead_smooth i hu) (hball i)]
    funext x
    exact (A.tensorPlaneEncode_weight i u x).symm
  have he : (fun i => combinedQuadraticMean (P i) ε (G i) (φ i)
      (fun j => (d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) τ 0) =
      δ^2 • (A.tensorPlaneEncode u +
        (fun i => chartedFamilyMean (n := n i) (ι := Fin 3) (P := P i) (ε := ε) (τ := τ) (s := s) (G := G i) (hG := hG i) (φ := φ i) (K := K i) (c := c i) (r := r i) (ρ := ρ) (R := R) (reference := reference i) (d i) hρ δ q (A.tensorPlaneRead i u))) := by
    funext i
    rw [charted_family_zero_phase_identity (d i) hρ hδ hτ q, hleading i]
    rfl
  rw [he, A.tensorPlaneRestore_smul, A.tensorPlaneRestore_add, A.tensorPlaneRestore_encode u hsym]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
