import OAI.Geometry.SurfaceImmersion.Atlas.UniformNearbyPhaseCancellation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

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

local instance nearbyPhaseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance nearbyPhaseFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance nearbyPhaseDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance nearbyPhaseDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance nearbyPhaseSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nearbyPhaseSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

/-- Fixed good-phase geometry gives uniform global cancellation for nearby
maps with the specified shifted derivative profiles at the actual slow scale. -/
theorem atlas_nearby_phase_cancellation_all_profiles
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
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
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        (∀ i m l, l ≤ m + 2 → WeightedEstimates.WeightedBound univ 1 l
          (R i m / (s : ℝ) ^ (l - 2)) (spaceCoordinates ∘ A.vectorPlaneRead i G)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ / s) ^ (q + 1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  have hlocal (i : A.centers) (j : ι i) :=
    PhaseGeometry.uniform_nearby_good_phase_cancellation_all_profiles (A.jetChartMap_smooth i hF)
      (hφ i j) (modeSupport (K i j))
      (by simpa only [A.jetChartMap_plane] using hImm i j)
      (by simpa only [A.jetChartMap_plane] using hgood i j)
  choose ρ hρ hall using hlocal
  refine ⟨ρ,hρ,?_⟩
  intro R hR q
  choose Cv Ct hCv hCt solve using fun i j => hall i j (R i) (hR i) q
  choose Dv hDv hv using fun m => A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  choose Dt hDt ht using fun m => A.global_linearized_residual_bound m
  refine ⟨fun i j m => Dv m * Cv i j m, fun i j m => Dt m * Ct i j m,
    fun i j m => mul_nonneg (hDv m) (hCv i j m),
    fun i j m => mul_nonneg (hDt m) (hCt i j m), ?_⟩
  intro G hG B hB hBρ hnear τ s hτ hs hτs hs1 hprefix target
  choose X hX hsp hb hr using fun i j => solve i j (A.jetChartMap i G)
    (A.jetChartMap_smooth i hG) (B i j) (hB i j) (hBρ i j)
    (by simpa only [A.jetChartMap_plane] using hnear i j) τ s hτ hs hτs hs1
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
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)
  let t : A.centers → ℕ → ℝ := fun i m => ∑ j, Ct i j m *
    supportedWeightedSeminorm (modeSupport (K i j)) s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)
  have hvn (i : A.centers) (m : ℕ) : 0 ≤ v i m :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCv i j m) (apply_nonneg _ _))
  have htn (i : A.centers) (m : ℕ) : 0 ≤ t i m :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hCt i j m) (apply_nonneg _ _))
  have hsize (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m (v i m) (Y i) :=
    WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ _ _
      (fun j _ => (hX i j).contDiffOn) (fun j _ => hb i j m)
  have hlin (i : A.centers) :
      RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) (Y i) =
        fun x => ∑ j, RealModes.realLinearizedTensor
          (spaceCoordinates ∘ A.vectorPlaneRead i G) (X i j) x := by
    simpa only [coordinateFullLinearized_unperturbed, A.jetChartMap_plane] using
      coordinateFullLinearized_sum emptyMetricPolynomial 0 (A.jetChartMap i G)
        Finset.univ (X i) (hX i)
  have hres (i : A.centers) (m : ℕ) : WeightedEstimates.WeightedBound univ τ m
      ((τ / s) ^ (q + 1) * t i m)
      (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) (Y i) + T i) := by
    have he : (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) (Y i) + T i) =
        fun x => ∑ j, (RealModes.realLinearizedTensor
          (spaceCoordinates ∘ A.vectorPlaneRead i G) (X i j) x +
            QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x) := by
      funext x
      rw [Pi.add_apply, hlin]
      exact Finset.sum_add_distrib.symm
    rw [he]
    have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hτ.le Finset.univ
      (fun j => (τ / s) ^ (q + 1) * Ct i j m *
        supportedWeightedSeminorm (modeSupport (K i j)) s
          (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j))
      (fun j => RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) (X i j) +
        QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j))
      (fun j _ => (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
        (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).contDiffOn
        (hX i j).contDiffOn).add (hd i j).contDiffOn)
      (fun j _ => by simpa only [A.jetChartMap_plane] using hr i j m)
    simpa only [t, Finset.mul_sum, mul_assoc, Pi.add_apply] using hsum
  refine ⟨A.vectorPlaneRestore Y, A.vectorPlaneRestore_smooth Y hY, ?_, ?_⟩
  · intro m
    have hh := hv m Y τ (∑ i, v i m) hτ (hτs.trans hs1)
      (Finset.sum_nonneg (fun i _ => hvn i m)) hY
      (fun i => (hsize i m).mono_const
        (Finset.single_le_sum (fun k _ => hvn k m) (Finset.mem_univ i)))
    simpa only [v, Finset.mul_sum, mul_assoc] using hh
  · intro m
    have hη : 0 ≤ (τ / s) ^ (q + 1) := pow_nonneg (div_nonneg hτ.le hs.le) _
    have hh := ht m G hG Y hY hYs T hT τ ((τ / s) ^ (q + 1) * ∑ i, t i m)
      hτ (hτs.trans hs1) (mul_nonneg hη (Finset.sum_nonneg (fun i _ => htn i m)))
      (fun i => (hres i m).mono_const (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun k _ => htn k m) (Finset.mem_univ i)) hη))
    have he : Dt m * ((τ / s) ^ (q + 1) * ∑ i, t i m) =
        (τ / s) ^ (q + 1) * ∑ i : A.centers, ∑ j, (Dt m * Ct i j m) *
          supportedWeightedSeminorm (modeSupport (K i j)) s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j) := by
      calc
        _ = (τ / s) ^ (q + 1) * (Dt m * ∑ i, t i m) := by ring
        _ = _ := by simp only [t, Finset.mul_sum, mul_assoc]
    rw [he] at hh
    exact hh

/-- Fixed good-phase geometry gives uniform global cancellation for nearby
maps with the specified shifted derivative profiles at the actual slow scale. -/
theorem atlas_nearby_phase_cancellation
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
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
    (R : A.centers → ℕ → ℝ) (hR : ∀ i m, 0 ≤ R i m) (q : ℕ) :
    ∃ (ρ : (i : A.centers) → ι i → ℝ)
      (C D : (i : A.centers) → ι i → ℕ → ℝ),
      (∀ i j, 0 < ρ i j) ∧ (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G)
        (B : (i : A.centers) → ι i → ℝ),
        (∀ i j, 0 ≤ B i j) → (∀ i j, B i j < ρ i j) →
        (∀ i j, WeightedEstimates.WeightedBound univ 1 2 (B i j)
          ((spaceCoordinates ∘ A.vectorPlaneRead i G) -
            (spaceCoordinates ∘ A.vectorPlaneRead i F))) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        (∀ i m l, l ≤ m + 2 → WeightedEstimates.WeightedBound univ 1 l
          (R i m / (s : ℝ) ^ (l - 2)) (spaceCoordinates ∘ A.vectorPlaneRead i G)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ / s) ^ (q + 1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  obtain ⟨ρ,hρ,hall⟩ := A.atlas_nearby_phase_cancellation_all_profiles F hF φ hφ K hK hImm hgood
  obtain ⟨C,D,hC,hD,hcancel⟩ := hall R hR q
  exact ⟨ρ,C,D,hρ,hC,hD,hcancel⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
