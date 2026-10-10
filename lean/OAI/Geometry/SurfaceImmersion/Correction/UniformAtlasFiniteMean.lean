import OAI.Geometry.SurfaceImmersion.Correction.UniformAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorFiniteMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorSymmetricMean

namespace OAI

/-! Finite adjustment of the actual global charted means.
The threshold precedes the local solvers, frequency and amplitude. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance uniformFiniteAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformFiniteAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformFiniteAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformFiniteAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformFiniteAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformFiniteAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_finite_mean
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R r r₀ : ℝ} {s : ℝ≥0}
    (hρ : 0 < ρ) (hr : 0 ≤ r) (hgap : r₀ < r) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (reference H : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H x)))
    (hsym : ∀ x v w, H x v w = H x w v)
    (hH0 : ∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r₀)
    (C : ℕ → ℝ) (hC : ∀ m, 1 ≤ C m)
    (hHC : ∀ m, A.TensorWeightedBound s m (C m) H) (q steps : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∃ β κ : ℕ → ℝ → ℝ,
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ {ε τ : ℝ}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ loss ≤ η₀ → ∀ δ : ℝ, 0 < δ → ∀ j ≤ steps,
      let u := A.tensorMeanTrial H (A.atlasMean (fun i => (d i).mean hρ δ q)) j
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) ∧
      (∀ x v w, u x v w = u x w v) ∧
      InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
      (∀ i, InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) (A.tensorPlaneRead i u)) ∧
      (∀ m, A.TensorWeightedBound s m (sizeBound L C β j m) u) ∧
      (∀ m, A.TensorWeightedBound s m
        (differenceBound L C β κ j m * (τ / s + ε / τ ^ loss)^(j+1))
        (u + A.atlasMean (fun i => (d i).mean hρ δ q) u - H)) := by
  obtain ⟨D₀,hD₀,hball,β,κ,hm⟩ := A.uniform_atlas_mean_majorants (R := R) p hρ hr reference href q
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := A.tensor_finite_mean_substitution hs hgap hC hH hH0 hHC steps
    (B := β) (K := κ)
  refine ⟨D₀,hD₀,β,κ,η₀,hη₀,hη₁,?_⟩
  intro ε τ d hd hτ hτs hε hε1 hsmall δ hδ j hj
  have hη : 0 < τ / s + ε / τ ^ Finset.univ.sup (fun i : A.centers => tensorLoss (P i)) :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨hu,hb,hsize,herror⟩ := ht _ hη hsmall _
    (hm d hd hτ hs hτs hs1 hε hε1 (hsmall.trans hη₁) δ hδ) j hj
  refine ⟨hu,A.tensorMeanTrial_symmetric H _ hsym
    (fun v _ => A.atlasMean_symmetric _ v) j,hb,?_,hsize,herror⟩
  intro i
  have hh := hball _ (A.tensorEncode_smooth hu) hb i
  rwa [A.tensorDecode_encode] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
