import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorFiniteMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorSymmetricMean

namespace OAI

/-! Finite nonlinear mean adjustment for the actual global atlas operator.
All local trial radii and the smallness threshold precede the local maps. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance atlasFiniteFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasFiniteFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasFiniteDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasFiniteDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasFiniteSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasFiniteSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem tensor_atlas_finite_mean {s r r₀ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hr : 0 ≤ r) (hgap : r₀ < r) (reference H : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H x)))
    (hsym : ∀ p v w, H p v w = H p w v)
    (hH0 : ∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r₀)
    (L : ℕ) (B K : ℕ → ℝ → ℝ) (C : ℕ → ℝ)
    (hB : ∀ m c, 1 ≤ c → 1 ≤ B m c) (hK : ∀ m c, 1 ≤ c → 1 ≤ K m c)
    (hC : ∀ m, 1 ≤ C m) (hHC : ∀ m, A.TensorWeightedBound s m (C m) H) (steps : ℕ) :
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∃ β κ : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor,
      (∀ i f, ContDiff ℝ ∞ f → InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) f →
        ContDiff ℝ ∞ (μ i f)) →
      (∀ i m c f, 1 ≤ c → ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) f →
        WeightedBound univ s (m+L) c f → WeightedBound univ s m (η * B m c) (μ i f)) →
      (∀ i m c d f g, 1 ≤ c → 0 ≤ d → ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) f →
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) g →
        WeightedBound univ s (m+L) c f → WeightedBound univ s (m+L) c g →
        WeightedBound univ s (m+L) d (f-g) →
        WeightedBound univ s m (K m c * η * d) (μ i f - μ i g)) →
      ∀ j ≤ steps,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun p => TotalSpace.mk' TensorFiber p (A.tensorMeanTrial H (A.atlasMean μ) j p)) ∧
        (∀ p v w, A.tensorMeanTrial H (A.atlasMean μ) j p v w =
          A.tensorMeanTrial H (A.atlasMean μ) j p w v) ∧
        InTrialBall univ (A.tensorEncode reference) r
          (A.tensorEncode (A.tensorMeanTrial H (A.atlasMean μ) j)) ∧
        (∀ i, InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r)
          (A.tensorPlaneRead i (A.tensorMeanTrial H (A.atlasMean μ) j))) ∧
        (∀ m, A.TensorWeightedBound s m (sizeBound L C β j m)
          (A.tensorMeanTrial H (A.atlasMean μ) j)) ∧
        (∀ m, A.TensorWeightedBound s m (differenceBound L C β κ j m * η^(j+1))
          (A.tensorMeanTrial H (A.atlasMean μ) j +
            A.atlasMean μ (A.tensorMeanTrial H (A.atlasMean μ) j) - H)) := by
  obtain ⟨D₀,hD₀,hlocal,β,κ,hm⟩ := A.atlasMean_majorants hr reference href L B K hB hK
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := A.tensor_finite_mean_substitution hs hgap hC hH hH0 hHC steps
    (B := β) (K := κ) (L := L)
  refine ⟨D₀,hD₀,β,κ,η₀,hη₀,hη₁,?_⟩
  intro η hη hsmall μ hsm hv hd j hj
  obtain ⟨htr,hball,hsize,herror⟩ := ht η hη hsmall (A.atlasMean μ)
    (hm hs hs1 η hη μ hsm hv hd) j hj
  refine ⟨htr,A.tensorMeanTrial_symmetric H (A.atlasMean μ) hsym
    (fun u _ => A.atlasMean_symmetric μ u) j,hball,?_,hsize,herror⟩
  intro i
  have hb := hlocal (A.tensorEncode (A.tensorMeanTrial H (A.atlasMean μ) j))
    (A.tensorEncode_smooth htr) hball i
  rwa [A.tensorDecode_encode] at hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
