import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeMetric
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialChartedSeed
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! Actual complex amplitude bounds for arbitrary finite phase families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialAtlasSeedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAtlasSeedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAtlasSeedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAtlasSeedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialAtlasSeedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasSeedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_finite_atlas_seed (q m : ℕ) :
    ∃ (p : ℕ) (E D : ℝ), 1 ≤ E ∧ 0 ≤ D ∧
    ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      ∀ C J : ℕ → ℝ,
      (∀ i j, (c i j).C = C ∧ (c i j).J = J ∧ ∀ k, (c i j).D k = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      (∀ i j, (d i j).budgets.inv (m+q+1) ≤ B ∧ (d i j).budgets.forms (m+q+1) ≤ B ∧
        (d i j).budgets.psi (m+q+1) ≤ B) →
      ∀ N : ℕ → ℝ, (∀ k, 0 ≤ N k) →
      (∀ i j, (d i j).budgets.normal (m+q+1) ≤ N (m+q+1)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i, WeightedEstimates.WeightedBound univ s (m+q+1) B (A.tensorPlaneRead i u)) →
      ∀ k i j, WeightedEstimates.WeightedBound univ s m
        (D*metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ))
        (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u i j)) := by
  classical
  obtain ⟨p,E,hE,hseed⟩ := polynomial_charted_seed_bounds q m
  choose D hD hd using fun k i : A.centers =>
    A.localize_outer_restore_bound (V := Fin 4 → ℂ) k i m
  let D₀ := ∑ k : A.centers, ∑ i : A.centers, D k i
  have hD₀ : 0 ≤ D₀ := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => hD k i
  refine ⟨p,E,D₀,hE,hD₀,?_⟩
  intro ι _ F hF φ K τ s c r ρ R reference d C J hc hρ hτ hs hτs hs1 B hB hρB hb N hN hnormal δ hδ u hu hball hbu k i j
  have hh := hseed (d i j) (hc i j).2.2 hρ hτ hs hτs hs1 B hB hρB
    (hb i j).1 (hb i j).2.1 (hb i j).2.2 N hN (hnormal i j) δ hδ
    (A.tensorPlaneRead i u) (A.tensorPlaneRead_smooth i hu) (hball i) (hbu i)
  have hC : (c i j).C = C := (hc i j).1
  have hJ : (c i j).J = J := (hc i j).2.1
  rw [hC,hJ] at hh
  have hsize : 0 ≤ metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ) := by
    have hbgt := correctedSeedBudget_nonneg 0 (c i j).C (fun _ => 0)
      (c i j).nonnegC q m (hN (m+q+1))
    have hjgt := (c i j).oneLEJ m
    rw [hC] at hbgt
    rw [hJ] at hjgt
    unfold metricFreeSizeBudget
    positivity
  have hout := hd k i ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) s
    (metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ)) hs hs1 hsize
    (((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff) hh
  have hsm := restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff)
  have hplane := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth k hsm) hout
  change WeightedEstimates.WeightedBound univ s m
    (D k i*(metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ)))
    (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u i j)) at hplane
  apply hplane.mono_const
  have hDi : D k i ≤ D₀ := (Finset.single_le_sum (fun j _ => hD k j)
    (Finset.mem_univ i)).trans (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun j _ => hD k j) (Finset.mem_univ k))
  calc
    _ ≤ D₀*(metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ)) :=
      mul_le_mul_of_nonneg_right hDi hsize
    _ = _ := by ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
