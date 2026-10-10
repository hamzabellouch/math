import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedGeometricSolver

namespace OAI

/-! Assemble actual local supported corrections. Atlas constants are chosen before the phase family and its cardinality. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance localCorrectionAssemblyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance localCorrectionAssemblyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance localCorrectionAssemblyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance localCorrectionAssemblyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance localCorrectionAssemblySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance localCorrectionAssemblySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_local_correction_assembly :
    ∃ Dv Dt : ℕ → ℝ, (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : (i : A.centers) → ι i → SmallModes.Base → ℝ)
        (_hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
        (K : (i : A.centers) → ι i → TopologicalSpace.Compacts SmallModes.Base),
      (∀ i j, (K i j : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ (X : (i : A.centers) → ι i → RealModes.RField 4),
      (∀ i j, ContDiff ℝ ∞ (X i j)) → (∀ i j, tsupport (X i j) ⊆ K i j) →
      ∀ (target : ∀ i j, SupportedField (F := ComplexTensor) (K i j))
        (Cv Ct : (i : A.centers) → ι i → ℕ → ℝ),
      (∀ i j m, 0 ≤ Cv i j m) → (∀ i j m, 0 ≤ Ct i j m) →
      (∀ i j m, WeightedEstimates.WeightedBound univ τ m (Cv i j m) (X i j)) →
      (∀ i j m, WeightedEstimates.WeightedBound univ τ m (Ct i j m)
        (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (X i j) +
          QuadraticMean.displacement τ (φ i j) (target i j))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (Dv m*∑ i : A.centers, ∑ j, Cv i j m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (Dt m*∑ i : A.centers, ∑ j, Ct i j m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (φ i j) (target i j) x))) := by
  classical
  choose Dv hDv hv using fun m => A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  choose Dt hDt ht using fun m => A.global_linearized_residual_bound m
  refine ⟨Dv,Dt,hDv,hDt,?_⟩
  intro ι inst F hF φ hφ K hK τ hτ hτ1 X hX hsp target Cv Ct hCv hCt hsize hres
  let Y : A.centers → RealModes.RField 4 := fun i x => ∑ j, X i j x
  have hY (i : A.centers) : ContDiff ℝ ∞ (Y i) := ContDiff.sum (fun j _ => hX i j)
  have hYs (i : A.centers) : tsupport (Y i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    apply closure_minimal _ (modeSupport (A.chartWeightCompact i)).isCompact.isClosed
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    exact image_eq_zero_of_notMem_tsupport (fun hj => hn (hK i j (hsp i j hj)))
  let T : A.centers → SmallModes.Base → Tensor := fun i x => ∑ j,
    QuadraticMean.displacement τ (φ i j) (target i j) x
  have htarget (i : A.centers) (j : ι i) : ContDiff ℝ ∞
      (QuadraticMean.displacement τ (φ i j) (target i j)) :=
    contDiffOn_univ.mp (RealModes.contDiffOn_displacement (hφ i j).contDiffOn
      (target i j).contDiff.contDiffOn τ)
  have hT (i : A.centers) : ContDiff ℝ ∞ (T i) := ContDiff.sum (fun j _ => htarget i j)
  have hvn (i : A.centers) (m : ℕ) : 0 ≤ ∑ j, Cv i j m :=
    Finset.sum_nonneg (fun j _ => hCv i j m)
  have htn (i : A.centers) (m : ℕ) : 0 ≤ ∑ j, Ct i j m :=
    Finset.sum_nonneg (fun j _ => hCt i j m)
  have hyv (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m
      (∑ j, Cv i j m) (Y i) :=
    WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ _ _
      (fun j _ => (hX i j).contDiffOn) (fun j _ => hsize i j m)
  have hlin (i : A.centers) :
      RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (Y i) =
        fun x => ∑ j, RealModes.realLinearizedTensor
          (spaceCoordinates ∘ A.vectorPlaneRead i F) (X i j) x := by
    simpa only [coordinateFullLinearized_unperturbed,A.jetChartMap_plane] using
      coordinateFullLinearized_sum emptyMetricPolynomial 0 (A.jetChartMap i F)
        Finset.univ (X i) (hX i)
  have hyr (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m
      (∑ j, Ct i j m)
      (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (Y i)+T i) := by
    have he : (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (Y i)+T i) =
        fun x => ∑ j, (RealModes.realLinearizedTensor
          (spaceCoordinates ∘ A.vectorPlaneRead i F) (X i j) x+
            QuadraticMean.displacement τ (φ i j) (target i j) x) := by
      funext x
      rw [Pi.add_apply,hlin]
      exact Finset.sum_add_distrib.symm
    rw [he]
    exact WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ _ _
      (fun j _ => (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
        (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn
        (hX i j).contDiffOn).add (htarget i j).contDiffOn)
      (fun j _ => hres i j m)
  refine ⟨A.vectorPlaneRestore Y,A.vectorPlaneRestore_smooth Y hY,?_,?_⟩
  · intro m
    apply hv m Y τ (∑ i : A.centers, ∑ j, Cv i j m) hτ hτ1
      (Finset.sum_nonneg (fun i _ => hvn i m)) hY
    intro i
    exact (hyv i m).mono_const
      (Finset.single_le_sum (fun k _ => hvn k m) (Finset.mem_univ i))
  · intro m
    apply ht m F hF Y hY hYs T hT τ (∑ i : A.centers, ∑ j, Ct i j m) hτ hτ1
      (Finset.sum_nonneg (fun i _ => htn i m))
    intro i
    exact (hyr i m).mono_const
      (Finset.single_le_sum (fun k _ => htn k m) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
