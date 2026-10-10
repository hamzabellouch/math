import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeMetric

namespace OAI

/-! The variable-family oscillation is the restoration of its local free sums. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

lemma finiteAtlasFreeOscillation_eq_restore
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.finiteAtlasFreeOscillation d hρ δ q u =
      A.vectorPlaneRestore (fun i => chartedFreeSum (d i) hρ δ q (A.tensorPlaneRead i u)) := by
  classical
  have hj (i : A.centers) (j : ι i) :
      restore (i : M) (A.outer i)
        ((d i j).displacement hρ δ q (A.tensorPlaneRead i u) ∘ planeCoordinateIsometry) =
      surfaceMode τ (A.finiteGlobalPhase (φ := φ) i j) (A.finiteGlobalAmplitude d hρ δ q u i j) := by
    have hh := A.restore_displacement i τ (coordinatePhase (φ i j))
      (coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))
      ((coordinateAmplitude_support _).trans (hK i j))
    simpa only [ChartedMeanData.displacement,PolynomialSolveData.freeDisplacement,
      ChartedMeanData.freeAmplitude,finiteGlobalPhase,finiteGlobalAmplitude,
      coordinatePhase,coordinateAmplitude,Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hh
  have hi (i : A.centers) :
      restore (i : M) (A.outer i)
        (chartedFreeSum (d i) hρ δ q (A.tensorPlaneRead i u) ∘ planeCoordinateIsometry) =
      ∑ j : ι i, surfaceMode τ (A.finiteGlobalPhase (φ := φ) i j)
        (A.finiteGlobalAmplitude d hρ δ q u i j) := by
    calc
      _ = ∑ j : ι i, restore (i : M) (A.outer i)
          ((d i j).displacement hρ δ q (A.tensorPlaneRead i u) ∘ planeCoordinateIsometry) := by
        funext p
        by_cases hp : p ∈ (chart (i : M)).source
        · simp only [restore,indicator_of_mem hp,Function.comp_apply,chartedFreeSum_eq,
            Finset.sum_apply,Finset.smul_sum]
        · simp only [restore,indicator_of_notMem hp,Finset.sum_apply,Finset.sum_const_zero]
      _ = _ := Finset.sum_congr rfl (fun j _ => hj i j)
  rw [finiteAtlasFreeOscillation,Fintype.sum_sigma]
  exact (Finset.sum_congr rfl (fun i _ => hi i)).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
