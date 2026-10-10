import OAI.Geometry.SurfaceImmersion.Correction.GlobalOscillatoryModes
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeOscillation

namespace OAI

/-! The finite free correction is an actual sum of globally smooth phase modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma coordinateAmplitude_support {K : TopologicalSpace.Compacts JetPolynomial.Base}
    (Z : SupportedField (F := Fin 4 → ℂ) K) :
    tsupport (coordinateAmplitude Z) ⊆ (modeSupport K : Set SmallModes.Base) :=
  (pushSupported planeCoordinateIsometry K Z).tsupport_subset

variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

/-- The outer cutoff makes the original local phase a globally smooth scalar. -/
def freeGlobalPhase
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (i : A.centers) (j : Fin 3) : M → ℝ :=
  restore (i : M) (A.outer i) ((d i).phase j)

/-- The global complex amplitude retains the original compact support. -/
def freeGlobalAmplitude
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : Fin 3) : M → Fin 4 → ℂ :=
  restore (i : M) (A.outer i) ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))

omit [CompactSpace M] in
lemma freeGlobalPhase_smooth
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (i : A.centers) (j : Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (A.freeGlobalPhase d i j) :=
  restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i) ((d i).solver j).smoothPhase

omit [CompactSpace M] in
lemma freeGlobalAmplitude_smooth
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : Fin 3) :
    ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (A.freeGlobalAmplitude d hρ δ q u i j) :=
  restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff

theorem atlas_free_global_modes
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.atlasFreeOscillation d hρ δ q u = ∑ i : A.centers, ∑ j : Fin 3,
      surfaceMode τ (A.freeGlobalPhase d i j) (A.freeGlobalAmplitude d hρ δ q u i j) := by
  classical
  unfold atlasFreeOscillation vectorPlaneRestore
  apply Finset.sum_congr rfl
  intro i _
  have he : (chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)) ∘ planeCoordinateIsometry =
      ∑ j : Fin 3, (QuadraticMean.displacement τ (coordinatePhase ((d i).phase j))
        (coordinateAmplitude ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) ∘
          planeCoordinateIsometry := by
    funext x
    simp only [chartedFreeSum,QuadraticMean.sumDisplacement,Function.comp_apply,Finset.sum_apply]
  rw [he]
  have hsum (f : Fin 3 → JetPolynomial.Base → RealModes.RVec 4) :
      restore (i : M) (A.outer i) (∑ j, f j) = ∑ j, restore (i : M) (A.outer i) (f j) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source <;>
      simp [restore,hp,Finset.smul_sum]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _
  have hs := (coordinateAmplitude_support
    ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))).trans (hK i j)
  simpa only [freeGlobalPhase,freeGlobalAmplitude,coordinatePhase,coordinateAmplitude,
    Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using A.restore_displacement i τ (coordinatePhase ((d i).phase j))
      (coordinateAmplitude ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))) hs

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
