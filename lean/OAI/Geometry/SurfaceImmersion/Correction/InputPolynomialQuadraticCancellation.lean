import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialInputCancellation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialTargetProfiles
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialOverlap

namespace OAI

/-! Uniform cancellation of the actual quadratic oscillations at a nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance inputPolynomialQuadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPolynomialQuadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputPolynomialQuadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputPolynomialQuadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputPolynomialQuadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputPolynomialQuadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem input_global_polynomial_quadratic_cancellation_all_profiles
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (φ i))
    (S : ι → Set M) (hS : ∀ i, IsClosed (S i))
    (hImm : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) x))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P a : ℕ → ℝ),
      (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ a m) → ∀ q : ℕ,
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ B : ℝ,
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ δ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 < δ →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 → (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (Z : ι → M → Fin 4 → ℂ) (_hZ : ∀ i, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z i)),
        (∀ i, tsupport (Z i) ⊆ S i) →
        (∀ k i m, WeightedEstimates.WeightedBound univ s (m+1) (a m*(δ*τ)) (A.vectorPlaneRead k (Z i))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2*η^(q+1)*Ct m)
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            (inducedTensor (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b))+
              A.atlasPolynomialQuadratic Pol ε G
                (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b)) -
              A.globalPolynomialQuadraticMean Q G ε τ φ Z))) := by
  classical
  obtain ⟨ρ,hρ,hall⟩ := A.atlas_polynomial_input_cancellation_all_profiles Pol Q hQ hlin F hF
    (A.globalQuadraticPhase φ) (A.globalQuadraticPhase_smooth φ hφ)
    (A.quadraticOverlapCompact S hS)
    (fun k l => Set.image_mono (A.quadraticOverlapCompact_subset S hS k l))
    hImm hgood U hU KU hUK
    (fun k l => (A.quadraticOverlapCompact_subset S hS k l).trans (hweight k))
  refine ⟨ρ,hρ,?_⟩
  intro P a hP ha q
  obtain ⟨T,hT,ht⟩ := A.atlas_polynomial_target_profiles Q hQ φ hφ U hU KU hUK hweight P a hP ha
  obtain ⟨C,D,hC,hD,hcancel⟩ := hall P hP q
  let N := fun k => PolynomialSolveData.inputOrder (P := Q k) q
  let Cv := fun m => ∑ k : A.centers, ∑ l, C k l m*T k (N k m)
  let Ct := fun m => ∑ k : A.centers, ∑ l, D k l m*T k (N k m)
  have hCv (m) : 0 ≤ Cv m := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hC k l m) (hT k (N k m))
  have hCt (m) : 0 ≤ Ct m := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hD k l m) (hT k (N k m))
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb τ δ ε η s hτ hs hτs hs1 hδ hε hε1 hη hη1 hsmall hp Z hZ hSZ hz
  let target := A.globalPolynomialQuadraticTargetRestricted Q hQ G hG ε τ φ Z hφ hZ S hS hSZ
  have htarget (k l m) : supportedWeightedSeminorm
      (modeSupport (A.quadraticOverlapCompact S hS k l)) s m (target k l) ≤ T k m*δ^2 := by
    apply supportedSeminorm_le_of_weightedBound hs (mul_nonneg (hT k m) (sq_nonneg δ))
    exact ht G hG Z hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1
      (fun i => (hsmall i).trans hη1) hp (fun i b m => (hz i b m).mono_order (Nat.le_succ m)) k m l
  obtain ⟨W,hW,hsize,hres⟩ := hcancel G hG B hB hBρ hb τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall hp target
  have hsum (E : (k : A.centers) → RealModes.QuadraticLabel ι → ℝ)
      (hE : ∀ k l, 0 ≤ E k l) (m : ℕ) :
      (∑ k : A.centers, ∑ l, E k l*supportedWeightedSeminorm
        (modeSupport (A.quadraticOverlapCompact S hS k l)) s (N k m) (target k l)) ≤
      δ^2*∑ k : A.centers, ∑ l, E k l*T k (N k m) := by
    calc
      _ ≤ ∑ k : A.centers, ∑ l, E k l*(T k (N k m)*δ^2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (htarget k l (N k m)) (hE k l)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    exact (hsize m k).mono_const (hsum (fun k l => C k l m) (fun k l => hC k l m) m)
  · intro m k
    have hh := (hres m k).mono_const
      (mul_le_mul_of_nonneg_left (hsum (fun k l => D k l m) (fun k l => hD k l m) m)
        (pow_nonneg hη _))
    have he : η^(q+1)*(δ^2*Ct m) = δ^2*η^(q+1)*Ct m := by ring
    rw [he] at hh
    have hsplit : inducedTensor (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b))+
        A.atlasPolynomialQuadratic Pol ε G (spaceCoordinates.symm ∘ ∑ b, surfaceMode τ (φ b) (Z b)) -
        A.globalPolynomialQuadraticMean Q G ε τ φ Z =
        A.tensorPlaneRestore (fun k x => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ k l))
            (target k l) x) := by
      rw [A.global_modes_full_quadratic Pol Q hQ hquad G hG ε τ φ Z hφ hZ]
      exact add_sub_cancel_left _ _
    rw [hsplit]
    exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
