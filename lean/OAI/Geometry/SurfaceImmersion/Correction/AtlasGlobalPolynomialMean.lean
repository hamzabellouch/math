import OAI.Geometry.SurfaceImmersion.Correction.RestoredQuadratureMean
import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalFreeModes
import OAI.Geometry.SurfaceImmersion.Geometry.TensorRestoreFinite
import OAI.Geometry.SurfaceImmersion.Correction.UnperturbedMeanIdentity
import OAI.Geometry.SurfaceImmersion.Correction.RestoredPolynomialModeMean
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeMetricSplit

namespace OAI

/-! The global finite phase expansion has the prescribed quadratic mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance globalPolynomialMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalPolynomialMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance globalPolynomialMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance globalPolynomialMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance globalPolynomialMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalPolynomialMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_global_polynomial_mean {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i))
    (hmap : ∀ i, (d i).G = A.jetChartMap i F)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.globalPolynomialQuadraticMean Q F ε τ
      (fun a : A.centers × Fin 3 => A.freeGlobalPhase d a.1 a.2)
      (fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2) =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) := by
  classical
  let Z₀ := fun (a : A.centers × Fin 3) (x : SmallModes.Base) =>
    RealModes.phaseZeroTensor τ (coordinatePhase ((d a.1).phase a.2))
      (coordinateAmplitude ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u))) x +
    (fun k => quadraticMeanCoefficient (Q a.1 k) ε (A.jetChartMap a.1 F)
      ((d a.1).phase a.2)
      ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)) τ 0
      (planeCoordinateIsometry.symm x))
  let T := fun (a : A.centers × Fin 3) (k : A.centers) (x : SmallModes.Base) =>
    (A.planeWeight k x)^2 •
      (RealModes.phaseZeroTensor τ
        (A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
        (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x +
      (fun j => quadraticMeanCoefficient (Q k j) ε (A.jetChartMap k F)
        (A.vectorChartRead k (A.freeGlobalPhase d a.1 a.2))
        (A.vectorChartRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) τ 0
        (planeCoordinateIsometry.symm x)))
  have ht (a : A.centers × Fin 3) : A.tensorPlaneRestore (T a) =
      A.bundleRestore A.tensorTriv a.1 (fun y => fiberFromThree (Z₀ a (planeCoordinateIsometry y))) := by
    have hs := (coordinateAmplitude_support
      ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u))).trans (hK a.1 a.2)
    have hp := A.restored_zeroPhase a.1 τ (coordinatePhase ((d a.1).phase a.2))
      (coordinateAmplitude ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
      (((d a.1).solver a.2).smoothPhase.comp planeCoordinateIsometry.symm.contDiff)
      ((((d a.1).data a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff.comp
        planeCoordinateIsometry.symm.contDiff) hs
    have hpoly := A.restored_polynomial_mode_mean P Q hrep F hF ε τ a.1
      (coordinatePhase ((d a.1).phase a.2))
      (coordinateAmplitude ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
      (((d a.1).solver a.2).smoothPhase.comp planeCoordinateIsometry.symm.contDiff)
      ((((d a.1).data a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff.comp
        planeCoordinateIsometry.symm.contDiff) hs
    have hT : T a =
        (fun k x => (A.planeWeight k x)^2 • RealModes.phaseZeroTensor τ
          (A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
          (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x) +
        (fun k x => (A.planeWeight k x)^2 • (fun j =>
          quadraticMeanCoefficient (Q k j) ε (A.jetChartMap k F)
            (A.vectorChartRead k (A.freeGlobalPhase d a.1 a.2))
            (A.vectorChartRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) τ 0
            (planeCoordinateIsometry.symm x))) := by
      funext k x
      exact smul_add _ _ _
    rw [hT,A.tensorPlaneRestore_add]
    have hp' : A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
        RealModes.phaseZeroTensor τ (A.vectorPlaneRead k (A.freeGlobalPhase d a.1 a.2))
          (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
        A.bundleRestore A.tensorTriv a.1 (fun y => fiberFromThree
          (RealModes.phaseZeroTensor τ (coordinatePhase ((d a.1).phase a.2))
            (coordinateAmplitude ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
            (planeCoordinateIsometry y))) := by
      simpa only [freeGlobalPhase,freeGlobalAmplitude,coordinatePhase,coordinateAmplitude,
        Function.comp_def,planeCoordinateIsometry.symm_apply_apply] using hp
    rw [hp']
    have hpoly' : A.polynomialModeMean Q F ε τ (A.freeGlobalPhase d a.1 a.2)
        (A.freeGlobalAmplitude d hρ δ q u a.1 a.2) =
        A.bundleRestore A.tensorTriv a.1 (fun y => fiberFromThree
          (fun k => quadraticMeanCoefficient (Q a.1 k) ε (A.jetChartMap a.1 F)
            ((d a.1).phase a.2)
            ((d a.1).data a.2 |>.freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)) τ 0 y)) := by
      simpa only [freeGlobalPhase,freeGlobalAmplitude,coordinatePhase,coordinateAmplitude,
        Function.comp_def,planeCoordinateIsometry.symm_apply_apply] using hpoly
    change _ + A.polynomialModeMean Q F ε τ _ _ = _
    rw [hpoly',← A.bundleRestore_add]
    congr 1
    funext y
    simp only [Pi.add_apply,Z₀,planeCoordinateIsometry.symm_apply_apply,map_add]
  have he : (fun k x => (A.planeWeight k x)^2 •
      combinedQuadraticMean (Q k) ε (A.jetChartMap k F)
        (fun a : A.centers × Fin 3 => A.vectorChartRead k (A.freeGlobalPhase d a.1 a.2))
        (fun a : A.centers × Fin 3 => A.vectorChartRead k (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) τ 0 x) =
        ∑ a : A.centers × Fin 3, T a := by
    funext k x j
    simp only [T,combinedQuadraticMean,RealModes.zeroPhaseSum,coordinateQuadraticMean,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Finset.mul_sum,
      Finset.sum_add_distrib,mul_add]
    rfl
  have hz (i : A.centers) : (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u) =
      ∑ j : Fin 3, Z₀ (i,j) := by
    ext x k
    simp only [ChartedMeanFamilyData.quadraticMean,combinedQuadraticMean,
      coordinateQuadraticMean,RealModes.zeroPhaseSum,Z₀,hmap,Pi.add_apply,
      Finset.sum_apply,Finset.sum_add_distrib]
  unfold globalPolynomialQuadraticMean
  rw [he,A.tensorPlaneRestore_sum]
  simp_rw [ht]
  rw [Fintype.sum_prod_type]
  funext p
  simp only [tensorPlaneRestore,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i]
  simp only [bundleRestore,Finset.sum_apply,map_sum,Finset.smul_sum]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
