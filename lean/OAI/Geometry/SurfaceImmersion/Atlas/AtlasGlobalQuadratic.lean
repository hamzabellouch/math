import OAI.Geometry.SurfaceImmersion.Correction.RestoredQuadratureMean
import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalFreeModes
import OAI.Geometry.SurfaceImmersion.Geometry.TensorRestoreFinite
import OAI.Geometry.SurfaceImmersion.Correction.UnperturbedMeanIdentity
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeMetricSplit

namespace OAI

/-! The global finite phase expansion has the quadratic mean determined by its phase data. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance globalFreeMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalFreeMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance globalFreeMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance globalFreeMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance globalFreeMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalFreeMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

theorem atlas_global_zeroPhase
    (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
      RealModes.zeroPhaseSum τ
        (fun a : A.centers × Fin 3 => A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
        (fun a : A.centers × Fin 3 => A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) := by
  classical
  let Z₀ := fun (a : A.centers × Fin 3) => RealModes.phaseZeroTensor τ
    (coordinatePhase ((d a.1).phase a.2))
    (coordinateAmplitude ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
  let T := fun (a : A.centers × Fin 3) (k : A.centers) (x : SmallModes.Base) =>
    (A.planeWeight k x)^2 • RealModes.phaseZeroTensor τ
      (A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
      (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x
  have ht (a : A.centers × Fin 3) : A.tensorPlaneRestore (T a) =
      A.bundleRestore A.tensorTriv a.1 (fun y => fiberFromThree (Z₀ a (planeCoordinateIsometry y))) := by
    have hs := (coordinateAmplitude_support
      ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u))).trans (hK a.1 a.2)
    have hh := A.restored_zeroPhase a.1 τ (coordinatePhase ((d a.1).phase a.2))
      (coordinateAmplitude ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
      (((d a.1).solver a.2).smoothPhase.comp planeCoordinateIsometry.symm.contDiff)
      ((((d a.1).data a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff.comp
        planeCoordinateIsometry.symm.contDiff) hs
    simpa only [T,Z₀,freeGlobalPhase,freeGlobalAmplitude,coordinatePhase,coordinateAmplitude,
      Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hh
  have he : (fun k x => (A.planeWeight k x)^2 •
      RealModes.zeroPhaseSum τ
        (fun a : A.centers × Fin 3 => A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
        (fun a : A.centers × Fin 3 => A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
      ∑ a : A.centers × Fin 3, T a := by
    funext k x
    simp only [T,RealModes.zeroPhaseSum,Finset.smul_sum,Finset.sum_apply]
  rw [he,A.tensorPlaneRestore_sum]
  simp_rw [ht]
  rw [Fintype.sum_prod_type]
  funext p
  simp only [tensorPlaneRestore,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ChartedMeanFamilyData.quadraticMean_unperturbed,RealModes.zeroPhaseSum,Z₀,
    bundleRestore,map_sum,Finset.smul_sum]

def atlasGlobalNonzero
    (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ∀ x : M, CovariantTwoTensor x := by
  classical
  exact A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
    RealModes.nonzeroPhaseSum τ
      (fun a : A.centers × Fin 3 => A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
      (fun a : A.centers × Fin 3 => A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x)

theorem atlas_free_global_metric
    (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u) =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) +
        A.atlasGlobalNonzero d hρ δ q u := by
  classical
  have hh := A.global_modes_metric τ
    (fun a : A.centers × Fin 3 => A.freeGlobalPhase d a.1 a.2)
    (fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2)
    (fun a => A.freeGlobalPhase_smooth d a.1 a.2)
    (fun a => A.freeGlobalAmplitude_smooth d hρ δ q u a.1 a.2)
  have he : (∑ a : A.centers × Fin 3,
      surfaceMode τ (A.freeGlobalPhase d a.1 a.2) (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) =
      A.atlasFreeOscillation d hρ δ q u := by
    rw [Fintype.sum_prod_type]
    exact (A.atlas_free_global_modes d hρ δ q u hK).symm
  rw [he,A.atlas_global_zeroPhase d hρ δ q u hK] at hh
  exact hh

theorem atlas_quadratic_oscillation_eq_global
    (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.atlasFreeQuadraticOscillation d hρ δ q u = A.atlasGlobalNonzero d hρ δ q u := by
  exact add_left_cancel ((A.atlas_free_metric_split d hρ δ q u hK).symm.trans
    (A.atlas_free_global_metric d hρ δ q u hK))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
