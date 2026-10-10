import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeRestore
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialChartedFreeFamily
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeResidual

namespace OAI

/-! Fixed-atlas polynomial free bounds for variable finite phase families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialAtlasFreeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAtlasFreeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAtlasFreeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAtlasFreeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialAtlasFreeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasFreeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_finite_atlas_free (q m : ℕ) :
    ∃ (p : ℕ) (E Dv Dt : ℝ), 1 ≤ E ∧ 0 ≤ Dv ∧ 0 ≤ Dt ∧
    ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)], ∀ n : ℕ,
      (∀ i, Fintype.card (ι i) ≤ n) →
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
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
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
      A.WeightedBound τ m
        (Dv*(n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ))
        (A.finiteAtlasFreeOscillation d hρ δ q u) ∧
      A.TensorWeightedBound τ m
        (Dt*(n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
        (linearMetricTensor F (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u)) := by
  classical
  obtain ⟨p,E,hE,hfree⟩ := polynomial_charted_free_family q m
  obtain ⟨Dv,hDv,hv⟩ := A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  obtain ⟨Dt,hDt,ht⟩ := A.tensorPlaneRestore_bound m
  refine ⟨p,E,Dv,Dt,hE,hDv,hDt,?_⟩
  intro ι _ n hn F hF φ K τ s c r ρ R reference d C J hc hρ hτ hs hτs hs1 hK B hB hρB hb N hN hnormal δ hδ u hu hball hbu
  let f := fun i => chartedFreeSum (d i) hρ δ q (A.tensorPlaneRead i u)
  have hf (i) : ContDiff ℝ ∞ (f i) := (chartedFreeSum_smooth_support (d i) hρ δ q _).1
  have hsp (i) : tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp ((chartedFreeSum_smooth_support (d i) hρ δ q _).2 hx)
    exact hK i j hj
  have hi (i) := hfree (d i) C J (hc i) hρ hτ hs hτs hs1 B hB hρB (hb i) N hN (hnormal i)
    δ hδ (A.tensorPlaneRead i u) (A.tensorPlaneRead_smooth i hu) (hball i) (hbu i)
  have hn' (i) : (Fintype.card (ι i) : ℝ) ≤ n := Nat.cast_le.mpr (hn i)
  have hEB : 0 ≤ E*B^p := mul_nonneg (zero_le_one.trans hE) (pow_nonneg (zero_le_one.trans hB) _)
  have hdt : 0 ≤ δ*τ := mul_nonneg hδ hτ.le
  have hη : 0 ≤ (τ/s)^(q+1) := pow_nonneg (div_nonneg hτ.le hs.le) _
  have hsize (i) : WeightedEstimates.WeightedBound univ τ m
      ((n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ)) (f i) := by
    apply (hi i).1.mono_const
    apply mul_le_mul_of_nonneg_right _ hdt
    apply mul_le_mul_of_nonneg_right _ hEB
    calc
      _ ≤ (Fintype.card (ι i) : ℝ)*max 1 (metricFreeSizeBudget C J N q m) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hn' i) (zero_le_one.trans (le_max_left _ _))
  have hres (i) : WeightedEstimates.WeightedBound univ τ m
      ((n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
      (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (f i)) := by
    have hh := (hi i).2
    simp only [coordinateFullLinearized_unperturbed,A.jetChartMap_plane] at hh
    apply hh.mono_const
    apply mul_le_mul_of_nonneg_right _ hdt
    apply mul_le_mul_of_nonneg_right _ hEB
    calc
      _ ≤ (Fintype.card (ι i) : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) hη)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hn' i) hη)
        (zero_le_one.trans (le_max_left _ _))
  rw [A.finiteAtlasFreeOscillation_eq_restore d hρ δ q u hK]
  constructor
  · have hh := hv f τ ((n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ))
      hτ (hτs.trans hs1) (by positivity) hf hsize
    convert hh using 1
    ring
  · rw [A.euclidean_vectorPlaneRestore_linearized hF f hf hsp]
    have hh := ht _ τ ((n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
      hτ (hτs.trans hs1) (by positivity)
      (fun i => contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
        (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn (hf i).contDiffOn)) hres
    convert hh using 1
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
