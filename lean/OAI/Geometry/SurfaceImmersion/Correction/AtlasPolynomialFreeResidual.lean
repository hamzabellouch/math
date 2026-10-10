import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeOscillation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLinearized
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedIncrementEstimate

namespace OAI

/-! Uniform global metric-linear residual of the actual free oscillation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance polynomialFreeResidualFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFreeResidualFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFreeResidualDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFreeResidualDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialFreeResidualSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFreeResidualSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_polynomial_free_residual
    {n : A.centers → ℕ} {mQ : ℕ}
    (Pglobal : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (P : A.centers → Fin 3 → Fin mQ → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (hrep : A.PolynomialLinearRepresentation Pglobal P)
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (q m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
      {ε τ η : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).G = A.jetChartMap i F) →
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → 0 ≤ η → η ≤ 1 →
      (∀ i, τ/s + ε/τ^tensorLoss (P i) ≤ η) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      A.TensorWeightedBound s N C u →
      A.TensorWeightedBound τ m (B*(δ*τ)*η^(q+1))
        (linearMetricTensor F (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u)+
          A.atlasPolynomialVariation Pglobal ε F
            (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u)) := by
  classical
  dsimp only
  let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i
    (PolynomialSolveData.inputOrder (P := P i) q m)
  let C' := fun i => max 1 (D i*C)
  choose B E hB hE hfree using fun i : A.centers =>
    uniform_charted_free_family (R := R) (r := r i) (reference := reference i) (p i) hρ q m (C' i)
  let S := 1 + ∑ i : A.centers, E i
  have hS (i : A.centers) : E i ≤ S := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := E) (fun i _ => zero_le_one.trans (hE i)) (Finset.mem_univ i)
    change E i ≤ 1 + ∑ i : A.centers, E i
    linarith
  have hS0 : 0 ≤ S := by
    have hh : 0 ≤ ∑ i : A.centers, E i := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hE i))
    change 0 ≤ 1 + ∑ i : A.centers, E i
    linarith
  obtain ⟨D₀,hD₀,hrestore⟩ := A.tensorPlaneRestore_bound m
  refine ⟨max 1 (D₀*S),le_max_left _ _,?_⟩
  intro F hF ε τ η s d hG hd hτ hs hτs hs1 hε hη hη1 hηle hK δ hδ u hu hball hbu
  have hlocal (i : A.centers) : WeightedEstimates.WeightedBound univ s
      (PolynomialSolveData.inputOrder (P := P i) q m) (C' i) (A.tensorPlaneRead i u) := by
    have horder : PolynomialSolveData.inputOrder (P := P i) q m ≤ N := Finset.le_sup
      (f := fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
      (Finset.mem_univ i)
    have hbu' : A.TensorWeightedBound s (PolynomialSolveData.inputOrder (P := P i) q m) C u :=
      fun k => (hbu k).mono_order horder
    exact (hread i u s C hs hs1 hC hu hbu').mono_const (le_max_right _ _)
  let f := fun i => chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)
  have hf (i : A.centers) : ContDiff ℝ ∞ (f i) :=
    (chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).1
  have hsp (i : A.centers) : tsupport (f i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp
      ((chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).2 hx)
    exact hK i j hj
  have hres (i : A.centers) : WeightedEstimates.WeightedBound univ τ m
      (S*(δ*τ)*η^(q+1))
      (coordinateFullLinearized (P i) ε (A.jetChartMap i F) (f i)) := by
    have hh := (hfree i (d i).data (hd i) hτ hs hτs hs1 hε
      ((hηle i).trans hη1) δ hδ
      (A.tensorPlaneRead i u) (zero_le_one.trans (le_max_left _ _))
      (A.tensorPlaneRead_smooth i hu) (hball i) (hlocal i)).2
    change WeightedEstimates.WeightedBound univ τ m
      (E i*(δ*τ)*(τ/s+ε/τ^tensorLoss (P i))^(q+1))
      (coordinateFullLinearized (P i) ε (d i).G (f i)) at hh
    rw [hG i] at hh
    apply hh.mono_const
    have hlocalη : 0 ≤ τ/s+ε/τ^tensorLoss (P i) :=
      add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hS i) (mul_nonneg hδ hτ.le))
      (pow_le_pow_left₀ hlocalη (hηle i) _) (pow_nonneg hlocalη _)
      (mul_nonneg hS0 (mul_nonneg hδ hτ.le))
  change A.TensorWeightedBound τ m _
    (linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f)+
      A.atlasPolynomialVariation Pglobal ε F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f))
  rw [hrep F hF f hf hsp ε]
  have hh := hrestore _ τ (S*(δ*τ)*η^(q+1)) hτ (hτs.trans hs1)
    (by positivity) (fun i => coordinateFullLinearized_smooth_global (hP i)
      (A.jetChartMap_smooth i hF) (hf i) ε) hres
  intro i
  apply (hh i).mono_const
  calc
    D₀*(S*(δ*τ)*η^(q+1)) = (D₀*S)*(δ*τ)*η^(q+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le))
      (pow_nonneg hη _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
