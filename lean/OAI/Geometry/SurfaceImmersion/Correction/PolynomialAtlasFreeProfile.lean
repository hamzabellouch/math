import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAtlasFree

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialFreeProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFreeProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFreeProfileDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFreeProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialFreeProfileSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFreeProfileSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


theorem polynomial_atlas_free_profile (q : ℕ) (C J N B : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m)) (hB : ∀ m, HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) :
    ∃ α β : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (α m)) ∧
      (∀ m, HasPolynomialBound (β m)) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      (n : ℕ), (∀ i, Fintype.card (ι i) ≤ n) →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, (c i j).C = (fun m => C m x) ∧
        (c i j).J = (fun m => J m x) ∧ ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ m, A.WeightedBound τ m (α m x*(n : ℝ)*(δ*τ))
          (A.finiteAtlasFreeOscillation d hρ δ q u) ∧
        A.TensorWeightedBound τ m ((τ/s)^(q+1)*(β m x*(n : ℝ)*(δ*τ)))
          (linearMetricTensor F (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u)) := by
  classical
  choose p E Dv Dt hE hDv hDt hfree using fun m => A.polynomial_finite_atlas_free q m
  let α := fun m x => Dv m*max 1 (metricFreeSizeBudget (fun j => C j x) (fun j => J j x)
    (fun j => N j x) q m)*(E m*(B (m+q+1) x)^(p m))
  let β := fun m x => Dt m*max 1 (metricFreeResidualBudget (fun j => C j x) (fun j => J j x)
    (fun j => N j x) q m)*(E m*(B (m+q+1) x)^(p m))
  have hα (m : ℕ) : HasPolynomialBound (α m) :=
    ((polynomialBound_const (hDv m)).mul
      ((polynomialBound_const zero_le_one).max
        (metricFreeSizeBudget_polynomial C J N hC hJ hN hC1 q m))).mul
          ((polynomialBound_const (zero_le_one.trans (hE m))).mul ((hB (m+q+1)).pow (p m)))
  have hβ (m : ℕ) : HasPolynomialBound (β m) :=
    ((polynomialBound_const (hDt m)).mul
      ((polynomialBound_const zero_le_one).max
        (metricFreeResidualBudget_polynomial C J N hC hJ hN hC1 q m))).mul
          ((polynomialBound_const (zero_le_one.trans (hE m))).mul ((hB (m+q+1)).pow (p m)))
  refine ⟨α,β,hα,hβ,?_⟩
  intro x hx ι _ n hn F hF φ K τ s c r ρ R reference d hc hρ hτ hs hτs hs1 hK hρB hb
    δ hδ u hu hball hbu m
  have hN0 (l : ℕ) : 0 ≤ N l x := by
    obtain ⟨_,_,_,hh⟩ := hN l
    exact (hh x hx).1
  have hh := hfree m n hn F hF d (fun l => C l x) (fun l => J l x) hc hρ hτ hs hτs hs1
    hK (B (m+q+1) x) (hB1 _ x hx) (hρB _)
    (fun i j => ⟨(hb i j _).1,(hb i j _).2.1,(hb i j _).2.2.1⟩)
    (fun l => N l x) hN0 (fun i j => (hb i j _).2.2.2)
    δ hδ u hu hball (fun i => hbu i _)
  constructor
  · convert hh.1 using 1
    dsimp [α]
    ring
  · convert hh.2 using 1
    dsimp [β]
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
