import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAtlasSeed

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialSeedProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSeedProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialSeedProfileDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSeedProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialSeedProfileSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSeedProfileSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


theorem polynomial_atlas_seed_profile (q : ℕ) (C J N B : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m)) (hB : ∀ m, HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) :
    ∃ α : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (α m)) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, (c i j).C = (fun m => C m x) ∧
        (c i j).J = (fun m => J m x) ∧ ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ k i j m, WeightedEstimates.WeightedBound univ s (m+1) (α m x*(δ*τ))
        (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u i j)) := by
  classical
  choose p E D hE hD hseed using fun m => A.polynomial_finite_atlas_seed q (m+1)
  let α := fun m x => D m*metricFreeSizeBudget (fun j => C j x) (fun j => J j x)
    (fun j => N j x) q (m+1) * (E m*(B ((m+1)+q+1) x)^(p m))
  have hα (m : ℕ) : HasPolynomialBound (α m) :=
    ((polynomialBound_const (hD m)).mul
      (metricFreeSizeBudget_polynomial C J N hC hJ hN hC1 q (m+1))).mul
        ((polynomialBound_const (zero_le_one.trans (hE m))).mul
          ((hB ((m+1)+q+1)).pow (p m)))
  refine ⟨α,hα,?_⟩
  intro x hx ι _ F hF φ K τ s c r ρ R reference d hc hρ hτ hs hτs hs1 hρB hb
    δ hδ u hu hball hbu k i j m
  have hN0 (l : ℕ) : 0 ≤ N l x := by
    obtain ⟨_,_,_,hh⟩ := hN l
    exact (hh x hx).1
  exact hseed m F hF d (fun l => C l x) (fun l => J l x) hc hρ hτ hs hτs hs1
    (B ((m+1)+q+1) x) (hB1 _ x hx) (hρB _)
    (fun i j => ⟨(hb i j _).1,(hb i j _).2.1,(hb i j _).2.2.1⟩)
    (fun l => N l x) hN0 (fun i j => (hb i j _).2.2.2)
    δ hδ u hu hball (fun i => hbu i _) k i j

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
