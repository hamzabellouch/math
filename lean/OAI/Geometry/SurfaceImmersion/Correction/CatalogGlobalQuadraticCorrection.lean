import OAI.Geometry.SurfaceImmersion.Atlas.AtlasCatalogCancellation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseCatalog
import OAI.Geometry.SurfaceImmersion.Geometry.CardinalityQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticTargetBudget

namespace OAI

/-! Actual global quadratic correction with explicit polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance catalogGlobalQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance catalogGlobalQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance catalogGlobalQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance catalogGlobalQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance catalogGlobalQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance catalogGlobalQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem catalog_global_quadratic_correction
    (V : Finset SmallModes.Base) {ε b D : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B α β : ℕ → ℝ → ℝ)
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x)
    (hα : ∀ m, RealModes.HasPolynomialBound (α m))
    (hβ : ∀ m, RealModes.HasPolynomialBound (β m)) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι], ∀ n : ℕ, Fintype.card ι ≤ n →
      ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (_hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        (S : ι → Set M) (hS : ∀ a, IsClosed (S a)),
      (∀ a, φ a ∈ A.linearPhaseCatalog V) → (∀ a, tsupport (Z a) ⊆ S a) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        ε*‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖ ≤
          ‖PhaseGeometry.secondQuadratic
            (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
            (-(phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).2,
              (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).1)‖) →
      (∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1)
        (α m x*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m
        (β m x) (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k y => (A.planeWeight k y)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) y))) := by
  classical
  obtain ⟨e,C,hC,hcancel⟩ := A.finite_catalog_atlas_cancellation
    (A.localQuadraticPhaseCatalog V) (A.localQuadraticPhaseCatalog_smooth V)
    hε hb hD hDB B hB hB1 q
  choose T hT ht using fun (k : A.centers) m =>
    cutoff_square_complex_bound (A.supportedPlaneWeight k) m
  let T₀ := fun m => ∑ k : A.centers, T k m
  have hT₀ (m : ℕ) : 0 ≤ T₀ m := Finset.sum_nonneg (fun k _ => hT k m)
  have hTT (k : A.centers) (m : ℕ) : T k m ≤ T₀ m :=
    Finset.single_le_sum (fun i _ => hT i m) (Finset.mem_univ k)
  let N := fun m => PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m
  let H := fun m x => (Fintype.card A.centers : ℝ)*(C m*x^(e m))*
    quadraticTargetBudget (N m) (T₀ (N m)) (α (N m) x) (β (N m) x)
  have hH (m : ℕ) : RealModes.HasPolynomialBound (H m) :=
    ((RealModes.polynomialBound_const (Nat.cast_nonneg _)).mul
      ((RealModes.polynomialBound_const (zero_le_one.trans (hC m))).mul
        (RealModes.polynomialBound_id.pow (e m)))).mul
      (quadraticTargetBudget_polynomial (N m) _ _ _
        (RealModes.polynomialBound_const (hT₀ _)) (hα _) (hβ _))
  choose d E hE hbound using hH
  refine ⟨d,E,hE,?_⟩
  intro ι inst dec n hn x hx F hF φ Z hφ hZ S hS hcat hSZ hImm hnormal hrel hgram
    τ δ s hτ hs hτs hs1 hδ hFj hz hp
  let : DecidableEq ι := dec
  let K := fun k l => modeSupport (A.quadraticOverlapCompact S hS k l)
  let target := A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ
  have hα0 (m : ℕ) : 0 ≤ α m x := by
    obtain ⟨_,_,_,hh⟩ := hα m
    exact (hh x hx).1
  have hβ0 (m : ℕ) : 0 ≤ β m x := by
    obtain ⟨_,_,_,hh⟩ := hβ m
    exact (hh x hx).1
  have htarget (k : A.centers) (l : RealModes.QuadraticLabel ι) (m : ℕ) :
      supportedWeightedSeminorm (K k l) s m (target k l) ≤
        quadraticTargetBudget m (T₀ m) (α m x) (β m x)*δ^2 := by
    have hcut : ∀ t : ℝ, 0 < t → t ≤ 1 → WeightedEstimates.WeightedBound univ t m (T₀ m)
        (fun y => ((A.supportedPlaneWeight k y*A.supportedPlaneWeight k y : ℝ) : ℂ)) :=
      fun t htpos ht1 => (ht k m t htpos ht1).mono_const (hTT k m)
    apply supportedSeminorm_le_of_weightedBound hs (by
      have hTn := hT₀ m
      dsimp [quadraticTargetBudget]
      positivity)
    exact cutoff_quadratic_bound_explicit (A.supportedPlaneWeight k) m (hT₀ m) hcut
      (α m x) (β m x) τ s δ (fun a => A.vectorPlaneRead k (φ a))
      (fun a => A.vectorPlaneRead k (Z a))
      (fun a => A.vectorPlaneRead_smooth k (hφ a))
      (fun a => A.vectorPlaneRead_smooth k (hZ a)) hτ hs hτs hs1 hδ
      (hα0 m) (hβ0 m) (fun a => hz k a m) (fun a v hv => hp k a m v hv) l
  obtain ⟨W,hW,hv,hr⟩ := hcancel x hx F hF
    (fun k l => coordinatePhase (A.globalQuadraticPhase φ k l))
    (A.globalQuadraticPhase_mem_catalog V φ hcat) K
    (fun k l => Set.image_mono (A.quadraticOverlapCompact_subset S hS k l))
    hImm hnormal hrel hgram τ s hτ hs hτs hs1 hFj target
  have hsum (m : ℕ) :
      (∑ k : A.centers, ∑ l : RealModes.QuadraticLabel ι,
        supportedWeightedSeminorm (K k l) s (N m) (target k l)) ≤
      (Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*
        (quadraticTargetBudget (N m) (T₀ (N m)) (α (N m) x) (β (N m) x)*δ^2) := by
    apply A.quadratic_family_sum_le hn _ _ (fun k l => htarget k l (N m))
    have ht0 := hT₀ (N m)
    dsimp [quadraticTargetBudget]
    positivity
  have hcoefficient (m : ℕ) :
      (C m*x^(e m))*(∑ k : A.centers, ∑ l : RealModes.QuadraticLabel ι,
        supportedWeightedSeminorm (K k l) s (N m) (target k l)) ≤
      δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m)) := by
    have hc0 : 0 ≤ C m*x^(e m) :=
      mul_nonneg (zero_le_one.trans (hC m)) (pow_nonneg (zero_le_one.trans hx) _)
    calc
      _ ≤ (C m*x^(e m))*((Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*
          (quadraticTargetBudget (N m) (T₀ (N m)) (α (N m) x) (β (N m) x)*δ^2)) :=
        mul_le_mul_of_nonneg_left (hsum m) hc0
      _ = δ^2*((n : ℝ)+2*(n : ℝ)^2)*H m x := by dsimp [H]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound m x hx).2 (by positivity)
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    exact (hv m k).mono_const (hcoefficient m)
  · intro m k
    have hh := (hr m k).mono_const (by
      have h := mul_le_mul_of_nonneg_left (hcoefficient m)
        (pow_nonneg (div_nonneg hτ.le hs.le) (q+1))
      simpa only [mul_assoc] using h)
    have he := A.globalQuadraticTarget_expansion τ φ Z hφ hZ
    have hrest : A.tensorPlaneRestore (fun i y =>
        ∑ j : RealModes.QuadraticLabel ι, QuadraticMean.displacement τ
          (coordinatePhase (A.globalQuadraticPhase φ i j)) (target i j) y) =
        A.tensorPlaneRestore (fun i y =>
        ∑ j : RealModes.QuadraticLabel ι, QuadraticMean.displacement τ
          (coordinatePhase (A.globalQuadraticPhase φ i j))
          (A.globalQuadraticTarget τ φ Z hφ hZ i j) y) := by
      congr 1
    rw [hrest] at hh
    rw [he]
    simpa only [mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
