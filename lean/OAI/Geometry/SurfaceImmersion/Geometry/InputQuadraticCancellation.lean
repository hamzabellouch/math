import OAI.Geometry.SurfaceImmersion.Atlas.AtlasInputPhaseCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticSolverInputBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseReadBounds

namespace OAI

/-! Uniform cancellation of the actual quadratic oscillations at a nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance inputQuadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputQuadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputQuadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputQuadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputQuadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputQuadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem input_global_quadratic_cancellation_all_profiles
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (φ i))
    (S : ι → Set M) (hS : ∀ i, IsClosed (S i))
    (hImm : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) x))
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P a : ℕ → ℝ),
      (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ a m) → ∀ q : ℕ,
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ B : ℝ,
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (Z : ι → M → Fin 4 → ℂ) (_hZ : ∀ i, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z i)),
        (∀ i, tsupport (Z i) ⊆ S i) →
        (∀ k i m, WeightedEstimates.WeightedBound univ s (m+1) (a m*(δ*τ)) (A.vectorPlaneRead k (Z i))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2*(τ/s)^(q+1)*Ct m)
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun i => A.vectorPlaneRead k (φ i))
                (fun i => A.vectorPlaneRead k (Z i)) x))) := by
  classical
  choose R hR hr using fun m => A.phase_read_gradient_bound φ hφ m
  obtain ⟨ρ,hρ,hall⟩ := A.atlas_input_phase_cancellation_all_profiles F hF
    (A.globalQuadraticPhase φ) (A.globalQuadraticPhase_smooth φ hφ)
    (A.quadraticOverlapCompact S hS)
    (fun k l => Set.image_mono (A.quadraticOverlapCompact_subset S hS k l))
    hImm hgood
  refine ⟨ρ,hρ,?_⟩
  intro P a hP ha q
  choose T hT ht using fun k m => A.globalQuadraticTarget_bound (ι := ι) k m (a m) (R m)
  obtain ⟨C,D,hC,hD,hcancel⟩ := hall P hP q
  let N := PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q
  let Cv := fun m => ∑ k : A.centers, ∑ l, C k l m*T k (N m)
  let Ct := fun m => ∑ k : A.centers, ∑ l, D k l m*T k (N m)
  have hCv (m) : 0 ≤ Cv m := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hC k l m) (hT k (N m))
  have hCt (m) : 0 ≤ Ct m := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hD k l m) (hT k (N m))
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb τ δ s hτ hs hτs hs1 hδ hp Z hZ hSZ hz
  let target := A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ
  have htarget (k l m) : supportedWeightedSeminorm
      (modeSupport (A.quadraticOverlapCompact S hS k l)) s m (target k l) ≤ T k m*δ^2 := by
    apply supportedSeminorm_le_of_weightedBound hs (mul_nonneg (hT k m) (sq_nonneg δ))
    exact ht k m τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ (ha m) (hR m)
      (fun i => hz k i m) (fun i v hv => hr m k i s hs.le hs1 v hv) l
  obtain ⟨W,hW,hsize,hres⟩ := hcancel G hG B hB hBρ hb τ s hτ hs hτs hs1 hp target
  have hsum (E : (k : A.centers) → RealModes.QuadraticLabel ι → ℝ)
      (hE : ∀ k l, 0 ≤ E k l) (m : ℕ) :
      (∑ k : A.centers, ∑ l, E k l*supportedWeightedSeminorm
        (modeSupport (A.quadraticOverlapCompact S hS k l)) s m (target k l)) ≤
      δ^2*∑ k : A.centers, ∑ l, E k l*T k m := by
    calc
      _ ≤ ∑ k : A.centers, ∑ l, E k l*(T k m*δ^2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (htarget k l m) (hE k l)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    exact (hsize m k).mono_const (hsum (fun k l => C k l m) (fun k l => hC k l m) (N m))
  · intro m k
    have hh := (hres m k).mono_const
      (mul_le_mul_of_nonneg_left (hsum (fun k l => D k l m) (fun k l => hD k l m) (N m))
        (pow_nonneg (div_nonneg hτ.le hs.le) _))
    have he : (τ/s)^(q+1)*(δ^2*Ct m) = δ^2*(τ/s)^(q+1)*Ct m := by ring
    rw [he] at hh
    rw [A.globalQuadraticTarget_expansion τ φ Z hφ hZ]
    exact hh

theorem input_global_quadratic_cancellation
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (φ i))
    (S : ι → Set M) (hS : ∀ i, IsClosed (S i))
    (hImm : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) x))
    (P a : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) (ha : ∀ m, 0 ≤ a m) (q : ℕ) :
    ∃ (ρ : ℝ) (Cv Ct : ℕ → ℝ), 0 < ρ ∧ (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ B : ℝ,
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (Z : ι → M → Fin 4 → ℂ) (_hZ : ∀ i, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z i)),
        (∀ i, tsupport (Z i) ⊆ S i) →
        (∀ k i m, WeightedEstimates.WeightedBound univ s (m+1) (a m*(δ*τ)) (A.vectorPlaneRead k (Z i))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2*(τ/s)^(q+1)*Ct m)
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun i => A.vectorPlaneRead k (φ i))
                (fun i => A.vectorPlaneRead k (Z i)) x))) := by
  obtain ⟨ρ,hρ,hall⟩ := A.input_global_quadratic_cancellation_all_profiles F hF φ hφ S hS hImm hgood
  obtain ⟨Cv,Ct,hCv,hCt,hcancel⟩ := hall P a hP ha q
  exact ⟨ρ,Cv,Ct,hρ,hCv,hCt,hcancel⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
