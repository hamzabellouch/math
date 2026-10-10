import OAI.Geometry.SurfaceImmersion.Correction.UniformAtlasFiniteMean
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasQuadraticResidual

namespace OAI

/-! Finite global adjustment of the actual quadratic zero phase. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance adjustedAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance adjustedAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance adjustedAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance adjustedAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance adjustedAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance adjustedAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_adjusted_quadratic_mean
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
      τ / s + ε / τ ^ loss ≤ η₀ →
      ∀ (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ),
      (∀ i j, w i j ≠ 0) →
      (∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j)) →
      (∀ i j x, x ∈ ((d i).solver j).e.source →
        ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
      (∀ i j x, x ∈ ((d i).solver j).e.source →
        ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
      (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
      ∀ δ : ℝ, 0 < δ → ∀ j ≤ steps, ∃ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) ∧
      (∀ x v w, u x v w = u x w v) ∧
      InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
      (∀ i, InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) (A.tensorPlaneRead i u)) ∧
      (∀ m, A.TensorWeightedBound s m (sizeBound L C β j m) u) ∧
      (∀ m, A.TensorWeightedBound s m
        (δ^2 * (differenceBound L C β κ j m * (τ / s + ε / τ ^ loss)^(j+1)))
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) := by
  obtain ⟨D₀,hD₀,β,κ,η₀,hη₀,hη₁,ht⟩ := A.uniform_atlas_finite_mean (R := R) p hρ hr hgap hs hs1
    reference H href hH hsym hH0 C hC hHC q steps
  refine ⟨D₀,hD₀,β,κ,η₀,hη₀,hη₁,?_⟩
  intro ε τ d hd hτ hτs hε hε1 hsmall Q w hw hphase hcutoff hform hsupport δ hδ j hj
  obtain ⟨hu,hsymu,hball,hlocal,hsize,herror⟩ :=
    ht d hd hτ hτs hε hε1 hsmall δ hδ j hj
  refine ⟨_,hu,hsymu,hball,hlocal,hsize,?_⟩
  intro m
  exact A.charted_family_atlas_quadratic_residual d hρ Q w hw hphase hcutoff hform hsupport
    _ H hu hH hsymu hlocal hδ.ne' hτ.ne' q (herror m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
