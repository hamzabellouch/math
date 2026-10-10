import OAI.Geometry.SurfaceImmersion.Atlas.AtlasGlobalQuadratic
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamily

namespace OAI

/-! Exact global free-mode identities for an arbitrary finite family in
each fixed atlas chart. This accommodates the variable number of grid cells. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance finiteAtlasFreeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteAtlasFreeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance finiteAtlasFreeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance finiteAtlasFreeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance finiteAtlasFreeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

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
local instance finiteAtlasIndexDecidable : DecidableEq (Σ i, ι i) := Classical.decEq _

def finiteGlobalPhase (i : A.centers) (j : ι i) : M → ℝ :=
  restore (i : M) (A.outer i) (φ i j)

def finiteGlobalAmplitude
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : ι i) : M → Fin 4 → ℂ :=
  restore (i : M) (A.outer i) ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))

def finiteAtlasFreeOscillation
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    M → RealModes.RVec 4 :=
  ∑ a : Σ i, ι i, surfaceMode τ (A.finiteGlobalPhase (φ := φ) a.1 a.2)
    (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)

omit [CompactSpace M] in
lemma finiteAtlasFreeOscillation_smooth
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞
      (A.finiteAtlasFreeOscillation d hρ δ q u) := by
  have hh := ContMDiff.sum (t := Finset.univ) (fun (a : Σ i, ι i) _ => surfaceMode_smooth τ
    (restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
      (c a.1 a.2).smoothPhase)
    (restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
      ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff))
  convert hh using 1
  funext x
  simp only [finiteAtlasFreeOscillation,finiteGlobalPhase,finiteGlobalAmplitude,Finset.sum_apply]

theorem finite_atlas_zeroPhase
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.zeroPhaseSum τ
      (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (fun a : Σ i, ι i => A.vectorPlaneRead k
        (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
    A.tensorPlaneRestore (fun i => RealModes.zeroPhaseSum τ
      (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) := by
  classical
  let Z₀ := fun (a : Σ i, ι i) => RealModes.phaseZeroTensor τ
    (coordinatePhase (φ a.1 a.2))
    (coordinateAmplitude ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
  let T := fun (a : Σ i, ι i) (k : A.centers) (x : SmallModes.Base) =>
    (A.planeWeight k x)^2 • RealModes.phaseZeroTensor τ
      (A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x
  have ht (a : Σ i, ι i) : A.tensorPlaneRestore (T a) =
      A.bundleRestore A.tensorTriv a.1 (fun y => fiberFromThree (Z₀ a (planeCoordinateIsometry y))) := by
    have hs := (coordinateAmplitude_support
      ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u))).trans (hK a.1 a.2)
    have hh := A.restored_zeroPhase a.1 τ (coordinatePhase (φ a.1 a.2))
      (coordinateAmplitude ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
      ((c a.1 a.2).smoothPhase.comp planeCoordinateIsometry.symm.contDiff)
      (((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff.comp
        planeCoordinateIsometry.symm.contDiff) hs
    simpa only [T,Z₀,finiteGlobalPhase,finiteGlobalAmplitude,coordinatePhase,coordinateAmplitude,
      Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hh
  have he : (fun k x => (A.planeWeight k x)^2 • RealModes.zeroPhaseSum τ
      (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (fun a : Σ i, ι i => A.vectorPlaneRead k
        (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) = ∑ a : Σ i, ι i, T a := by
    funext k x
    simp only [T,RealModes.zeroPhaseSum,Finset.smul_sum,Finset.sum_apply]
  rw [he,A.tensorPlaneRestore_sum]
  simp_rw [ht]
  rw [Fintype.sum_sigma]
  funext p
  simp only [tensorPlaneRestore,RealModes.zeroPhaseSum,Z₀,Finset.sum_apply,
    bundleRestore,map_sum,Finset.smul_sum]

theorem finite_atlas_free_metric
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
      δ^2 • A.tensorPlaneRestore (fun i =>
        chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) +
      A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
        (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
        (fun a : Σ i, ι i => A.vectorPlaneRead k
          (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) := by
  classical
  have hphase (a : Σ i, ι i) : ContMDiff planeModel 𝓘(ℝ) ∞
      (A.finiteGlobalPhase (φ := φ) a.1 a.2) :=
    restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1) (c a.1 a.2).smoothPhase
  have hamp (a : Σ i, ι i) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞
      (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2) :=
    restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
      ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff
  have hm := A.global_modes_metric τ
    (fun a : Σ i, ι i => A.finiteGlobalPhase (φ := φ) a.1 a.2)
    (fun a : Σ i, ι i => A.finiteGlobalAmplitude d hρ δ q u a.1 a.2) hphase hamp
  rw [A.finite_atlas_zeroPhase d hρ δ q u hK] at hm
  have hlocal (i : A.centers) : RealModes.zeroPhaseSum τ
      (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))) =
      δ^2 • (chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) := by
    have hz : combinedQuadraticMean (P i) 0 (G i) (φ i)
        (fun j => (d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) τ 0 =
        RealModes.zeroPhaseSum τ (fun j => coordinatePhase (φ i j))
          (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))) := by
      ext x k
      simp [combinedQuadraticMean,coordinateQuadraticMean,quadraticMeanCoefficient,conjugated]
    rw [← hz]
    exact charted_family_zero_phase_identity (d i) hρ hδ hτ q (A.tensorPlaneRead i u)
  have he : (fun i => RealModes.zeroPhaseSum τ (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) =
      δ^2 • (fun i => chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) := funext hlocal
  rw [he,A.tensorPlaneRestore_smul] at hm
  exact hm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
