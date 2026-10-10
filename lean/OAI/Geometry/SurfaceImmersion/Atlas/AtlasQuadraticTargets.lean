import OAI.Geometry.SurfaceImmersion.Atlas.AtlasGlobalQuadratic
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! Actual supported quadratic targets for the global phase expansion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance atlasQuadraticTargetsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticTargetsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasQuadraticTargetsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticTargetsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasQuadraticTargetsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticTargetsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def globalQuadraticPhase (φ : ι → M → ℝ) (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    JetPolynomial.Base → ℝ :=
  RealModes.quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l ∘ planeCoordinateIsometry

omit [Fintype ι] [DecidableEq ι] in
lemma globalQuadraticPhase_smooth (φ : ι → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    ContDiff ℝ ∞ (A.globalQuadraticPhase φ k l) :=
  (RealModes.quadraticPhase_smooth (fun a => A.vectorPlaneRead_smooth k (hφ a)) l).comp
    planeCoordinateIsometry.contDiff

def globalQuadraticTarget (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.chartWeightCompact k)) where
  toFun := fun x => (A.planeWeight k x)^2 • RealModes.quadraticAmplitude τ
    (fun a => A.vectorPlaneRead k (φ a)) (fun a => A.vectorPlaneRead k (Z a)) l x
  contDiff' := ((A.planeWeight_smooth k).pow 2).smul
    (RealModes.quadraticAmplitude_smooth (fun a => A.vectorPlaneRead_smooth k (hφ a))
      (fun a => A.vectorPlaneRead_smooth k (hZ a)) τ l)
  zero_on_compl' := by
    intro x hx
    have hw := (A.supportedPlaneWeight k).zero_on_compl hx
    change A.planeWeight k x = 0 at hw
    simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.zero_apply]

theorem globalQuadraticTarget_expansion (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)) :
    A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
      (fun a => A.vectorPlaneRead k (φ a)) (fun a => A.vectorPlaneRead k (Z a)) x) =
    A.tensorPlaneRestore (fun k x => ∑ l : RealModes.QuadraticLabel ι,
      QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ k l))
        (A.globalQuadraticTarget τ φ Z hφ hZ k l) x) := by
  congr 1
  funext k x
  rw [RealModes.nonzeroPhaseSum_eq_quadraticFamily]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change (A.planeWeight k x)^2 • QuadraticMean.realMode
    (RealModes.quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l x / τ)
    (RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
      (fun a => A.vectorPlaneRead k (Z a)) l x) = _
  simp only [QuadraticMean.displacement,coordinatePhase,globalQuadraticPhase,
    Function.comp_apply,LinearIsometryEquiv.apply_symm_apply,globalQuadraticTarget]
  exact (realMode_smul _ _ _).symm

theorem global_quadratic_cancellation
    {n : A.centers → ℕ}
    (P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression) :
    ∃ Dv Dt : ℕ → ℝ, (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        {τ : ℝ} {s : ℝ≥0}
        (c : ∀ k l, PolynomialSolveData (P k) 0 (A.jetChartMap k F)
          (A.jetChartMap_smooth k hF) (A.globalQuadraticPhase φ k l)
          (A.chartWeightCompact k) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → ∀ q : ℕ,
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (Dv m * ∑ k : A.centers, ∑ l, (c k l).size (A.globalQuadraticTarget τ φ Z hφ hZ k l) q m) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (Dt m * ∑ k : A.centers, ∑ l, (c k l).residual (A.globalQuadraticTarget τ φ Z hφ hZ k l) q m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) x))) := by
  classical
  obtain ⟨Dv,Dt,hDv,hDt,h⟩ := A.atlas_finite_cancellation
    (ι := fun _ => RealModes.QuadraticLabel ι) P
  refine ⟨Dv,Dt,hDv,hDt,?_⟩
  intro F hF φ Z hφ hZ τ s c hτ hs hτs hs1 q
  obtain ⟨W,hW,hsize,hres⟩ := h F hF (A.globalQuadraticPhase φ)
    (fun k _ => A.chartWeightCompact k) c hτ hs hτs hs1 (fun _ _ => Subset.rfl)
    (A.globalQuadraticTarget τ φ Z hφ hZ) q
  refine ⟨W,hW,hsize,?_⟩
  intro m
  rw [A.globalQuadraticTarget_expansion τ φ Z hφ hZ]
  exact hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
