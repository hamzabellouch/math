import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! The atlas restoration constants are fixed before the finite phase-label types. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance uniformFiniteAtlasSolveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformFiniteAtlasSolveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformFiniteAtlasSolveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformFiniteAtlasSolveDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformFiniteAtlasSolveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformFiniteAtlasSolveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_finite_atlas_cancellation
    {n : A.centers → ℕ}
    (P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression) :
    ∃ Dv Dt : ℕ → ℝ, (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : (i : A.centers) → ι i → JetPolynomial.Base → ℝ)
        (K : (i : A.centers) → ι i → TopologicalSpace.Compacts JetPolynomial.Base)
        {τ : ℝ} {s : ℝ≥0}
        (c : ∀ i j, PolynomialSolveData (P i) 0 (A.jetChartMap i F)
          (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)), ∀ q : ℕ,
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (Dv m * ∑ i : A.centers, ∑ j, (c i j).size (target i j) q m) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (Dt m * ∑ i : A.centers, ∑ j, (c i j).residual (target i j) q m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  choose Dv hDv hv using fun m => A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  choose Dt hDt ht using fun m => A.global_linearized_residual_bound m
  refine ⟨Dv,Dt,hDv,hDt,?_⟩
  intro ι inst F hF φ K τ s c hτ hs hτs hs1 hK target q
  have hsmall (i : A.centers) : τ/s + (0:ℝ)/τ^tensorLoss (P i) ≤ 1 := by
    simpa only [zero_div,add_zero] using (div_le_one₀ hs).mpr hτs
  choose X hX hsupport hsize hres using fun i : A.centers =>
    finite_polynomial_cancellation (P i) 0 (A.jetChartMap_smooth i hF) (φ i) (K i) (c i)
      hτ hs hτs hs1 (le_refl 0) (hsmall i) (target i) q
  have hsp (i : A.centers) : tsupport (X i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hsupport i hx)
    exact hK i j hj
  let T : A.centers → SmallModes.Base → Tensor := fun i x => ∑ j,
    QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x
  have hT (i : A.centers) : ContDiff ℝ ∞ (T i) := by
    apply ContDiff.sum
    intro j _
    exact contDiffOn_univ.mp (RealModes.contDiffOn_displacement
      ((c i j).smoothPhase.comp planeCoordinateIsometry.symm.contDiff).contDiffOn
      (target i j).contDiff.contDiffOn τ)
  have hsz (i : A.centers) (m : ℕ) : 0 ≤ ∑ j, (c i j).size (target i j) q m :=
    Finset.sum_nonneg (fun j _ => (c i j).size_nonneg (target i j) q m)
  have hrr (i : A.centers) (m : ℕ) : 0 ≤ ∑ j, (c i j).residual (target i j) q m :=
    Finset.sum_nonneg (fun j _ => (c i j).residual_nonneg
      (by simpa only [zero_div,add_zero] using (div_nonneg hτ.le hs.le)) (target i j) q m)
  refine ⟨A.vectorPlaneRestore X,A.vectorPlaneRestore_smooth X hX,?_,?_⟩
  · intro m
    apply hv m X τ (∑ i : A.centers, ∑ j, (c i j).size (target i j) q m)
      hτ (hτs.trans hs1) (Finset.sum_nonneg (fun i _ => hsz i m)) hX
    intro i
    exact (hsize i m).mono_const (Finset.single_le_sum (fun k _ => hsz k m) (Finset.mem_univ i))
  · intro m
    apply ht m F hF X hX hsp T hT τ (∑ i : A.centers, ∑ j, (c i j).residual (target i j) q m)
      hτ (hτs.trans hs1) (Finset.sum_nonneg (fun i _ => hrr i m))
    intro i
    have hr := hres i m
    simp_rw [coordinateFullLinearized_unperturbed, A.jetChartMap_plane] at hr
    exact hr.mono_const (Finset.single_le_sum (fun k _ => hrr k m) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
