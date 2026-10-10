import OAI.Geometry.SurfaceImmersion.Correction.UniformPolynomialNearbyCancellation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialCancellation

namespace OAI

/-!
Atlas cancellation uniform over a neighborhood of a fixed immersion.
The reference geometry, per-chart shifted profiles and finite phase family
determine all constants before the varying map, target or scale is chosen.
-/

noncomputable section

open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing

open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

local instance nearbyPhasePolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance nearbyPhasePolynomialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance nearbyPhasePolynomialDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance nearbyPhasePolynomialDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance nearbyPhasePolynomialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nearbyPhasePolynomialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

/-- Fixed good-phase geometry gives uniform global cancellation for nearby
maps with the specified shifted derivative profiles at the actual slow scale. -/
theorem atlas_polynomial_nearby_cancellation_all_profiles
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {nq : ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrepr : A.PolynomialLinearRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : (i : A.centers) → ι i → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (K : (i : A.centers) → ι i → TopologicalSpace.Compacts JetPolynomial.Base)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (hImm : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) p))
    (hgood : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) p)
        (phaseDerivative (coordinatePhase (φ i j)) p))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hUK : ∀ i, U i ⊆ KU i) (hKU : ∀ i j, (K i j : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ : (i : A.centers) → ι i → ℝ, (∀ i j, 0 < ρ i j) ∧
      ∀ (R : A.centers → ℕ → ℝ), (∀ i m, 0 ≤ R i m) → ∀ q : ℕ,
      ∃ C D : (i : A.centers) → ι i → ℕ → ℝ,
      (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G)
        (B : (i : A.centers) → ι i → ℝ),
        (∀ i j, 0 ≤ B i j) → (∀ i j, B i j < ρ i j) →
        (∀ i j, WeightedEstimates.WeightedBound univ 1 2 (B i j)
          ((spaceCoordinates ∘ A.vectorPlaneRead i G) -
            (spaceCoordinates ∘ A.vectorPlaneRead i F))) →
      ∀ (τ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 →
        (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ i m l, l ≤ m + 2 → WeightedEstimates.WeightedBound univ 1 l
          (R i m / (s : ℝ) ^ (l - 2)) (spaceCoordinates ∘ A.vectorPlaneRead i G)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (η ^ (q + 1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation P ε G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  have hlocal (i : A.centers) (j : ι i) :=
    PhaseGeometry.uniform_polynomial_nearby_cancellation_all_profiles (Q i) (hQ i) (A.jetChartMap_smooth i hF)
      (hφ i j) (modeSupport (K i j))
      (by simpa only [A.jetChartMap_plane] using hImm i j)
      (by simpa only [A.jetChartMap_plane] using hgood i j)
      (hU i) (KU i) (hUK i) (by
        rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa only [planeCoordinateIsometry.symm_apply_apply] using hKU i j hz)
  choose ρ hρ hall using hlocal
  refine ⟨ρ,hρ,?_⟩
  intro R hR q
  choose Cv Ct hCv hCt solve using fun i j => hall i j (R i) (hR i) q
  choose Dv hDv hv using fun m => A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  choose Dt hDt ht using fun m => A.tensorPlaneRestore_bound m
  refine ⟨fun i j m => Dv m * Cv i j m, fun i j m => Dt m * Ct i j m,
    fun i j m => mul_nonneg (hDv m) (hCv i j m),
    fun i j m => mul_nonneg (hDt m) (hCt i j m), ?_⟩
  intro G hG B hB hBρ hnear τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall hprefix target
  choose X hX hsp hb hr using fun i j => solve i j (A.jetChartMap i G)
    (A.jetChartMap_smooth i hG) (B i j) (hB i j) (hBρ i j)
    (by simpa only [A.jetChartMap_plane] using hnear i j) τ ε s hτ hs hτs hs1 hε hε1 ((hsmall i).trans hη1)
    (by simpa only [A.jetChartMap_plane] using hprefix i) (target i j)
  let Y : A.centers → RealModes.RField 4 := fun i x => ∑ j, X i j x
  have hY (i : A.centers) : ContDiff ℝ ∞ (Y i) :=
    ContDiff.sum (fun j _ => hX i j)
  have hYs (i : A.centers) : tsupport (Y i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    apply closure_minimal _ (modeSupport (A.chartWeightCompact i)).isCompact.isClosed
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    exact image_eq_zero_of_notMem_tsupport (fun hxj => hn (hK i j (hsp i j hxj)))
  let T : A.centers → SmallModes.Base → Tensor := fun i x => ∑ j,
    QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x
  have hd (i : A.centers) (j : ι i) : ContDiff ℝ ∞
      (QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j)) :=
    contDiffOn_univ.mp (RealModes.contDiffOn_displacement
      ((hφ i j).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
      (target i j).contDiff.contDiffOn τ)
  have hT (i : A.centers) : ContDiff ℝ ∞ (T i) := ContDiff.sum (fun j _ => hd i j)
  let v : A.centers → ℕ → ℝ := fun i m => ∑ j, Cv i j m *
    supportedWeightedSeminorm (modeSupport (K i j)) s
      (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)
  let t : A.centers → ℕ → ℝ := fun i m => ∑ j, Ct i j m *
    supportedWeightedSeminorm (modeSupport (K i j)) s
      (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)
  have hvn (i : A.centers) (m : ℕ) : 0 ≤ v i m :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCv i j m) (apply_nonneg _ _))
  have htn (i : A.centers) (m : ℕ) : 0 ≤ t i m :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCt i j m) (apply_nonneg _ _))
  have hsize (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m (v i m) (Y i) :=
    WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ _ _
      (fun j _ => (hX i j).contDiffOn) (fun j _ => hb i j m)
  have hlin (i : A.centers) :
      coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i) =
        fun x => ∑ j, coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (X i j) x := by
    exact coordinateFullLinearized_sum (Q i) ε (A.jetChartMap i G)
        Finset.univ (X i) (hX i)
  have hres (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m
      (η ^ (q + 1) * t i m)
      (coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i) + T i) := by
    have he : (coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i) + T i) =
        fun x => ∑ j, (coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (X i j) x +
            QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x) := by
      funext x
      rw [Pi.add_apply, hlin]
      exact Finset.sum_add_distrib.symm
    rw [he]
    have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun j => η ^ (q + 1) * Ct i j m *
        supportedWeightedSeminorm (modeSupport (K i j)) s
          (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
      (fun j => coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (X i j) +
        QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j))
      (fun j _ => (coordinateFullLinearized_smooth isOpen_univ isOpen_univ (Q i) (hQ i)
        (A.jetChartMap_smooth i hG) (fun _ _ => mem_univ _) (A.chartWeightCompact i)
        (subset_univ _) (hX i j) ((hsp i j).trans (hK i j)) ε).contDiffOn.add (hd i j).contDiffOn)
      (fun j _ => (hr i j m).mono_const (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
          (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _)))
          (hsmall i) (q+1)) (hCt i j m)) (apply_nonneg _ _)))
    simpa only [t, Finset.mul_sum, mul_assoc, Pi.add_apply] using hsum
  refine ⟨A.vectorPlaneRestore Y, A.vectorPlaneRestore_smooth Y hY, ?_, ?_⟩
  · intro m
    have hh := hv m Y τ (∑ i, v i m) hτ (hτs.trans hs1)
      (Finset.sum_nonneg (fun i _ => hvn i m)) hY
      (fun i => (hsize i m).mono_const
        (Finset.single_le_sum (fun k _ => hvn k m) (Finset.mem_univ i)))
    simpa only [v, Finset.mul_sum, mul_assoc] using hh
  · intro m
    have hηpow : 0 ≤ η ^ (q + 1) := pow_nonneg hη _
    rw [hrepr G hG Y hY hYs ε, ← A.tensorPlaneRestore_add]
    have hh := ht m (fun i => coordinateFullLinearized (Q i) ε (A.jetChartMap i G) (Y i)+T i)
      τ (η^(q+1) * ∑ i, t i m) hτ (hτs.trans hs1)
      (mul_nonneg hηpow (Finset.sum_nonneg (fun i _ => htn i m)))
      (fun i => (coordinateFullLinearized_smooth isOpen_univ isOpen_univ (Q i) (hQ i)
        (A.jetChartMap_smooth i hG) (fun _ _ => mem_univ _) (A.chartWeightCompact i)
        (subset_univ _) (hY i) (hYs i) ε).add (hT i))
      (fun i => (hres i m).mono_const (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun k _ => htn k m) (Finset.mem_univ i)) hηpow))
    have he : Dt m * (η^(q+1) * ∑ i, t i m) =
        η^(q+1) * ∑ i : A.centers, ∑ j, (Dt m * Ct i j m) *
          supportedWeightedSeminorm (modeSupport (K i j)) s
            (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j) := by
      calc
        _ = η^(q+1) * (Dt m * ∑ i, t i m) := by ring
        _ = _ := by simp only [t, Finset.mul_sum, mul_assoc]
    rw [he] at hh
    exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
