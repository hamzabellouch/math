import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialNearbyCancellation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseStability

namespace OAI

/-! Uniform atlas cancellation from the global norms used in the iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance inputPhasePolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPhasePolynomialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputPhasePolynomialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputPhasePolynomialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputPhasePolynomialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputPhasePolynomialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_input_cancellation_all_profiles
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrepr : A.PolynomialLinearRepresentation Pol Q)
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
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) → ∀ q : ℕ,
    ∃ C D : (i : A.centers) → ι i → ℕ → ℝ,
      (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 →
        (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (η^(q+1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  choose E hE he using fun (i : A.centers) m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  choose E₀ hE₀ he₀ using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i 2
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  obtain ⟨r,hr,hall⟩ := A.atlas_polynomial_nearby_cancellation_all_profiles Pol Q hQ hrepr F hF φ hφ K hK
    hImm hgood U hU KU hUK hKU
  have hL₀ (i) : 0 ≤ L*E₀ i := mul_nonneg (norm_nonneg _) (hE₀ i)
  obtain ⟨ρ,hρ,_,hρr⟩ := finite_positive_threshold
    (fun a : (i : A.centers) × ι i => r a.1 a.2/(1+L*E₀ a.1))
    (fun a => div_pos (hr a.1 a.2) (by linarith [hL₀ a.1]))
  refine ⟨ρ,hρ,?_⟩
  intro P hP q
  let R := fun i m => L*E i m*P m
  have hR (i m) : 0 ≤ R i m := mul_nonneg (mul_nonneg (norm_nonneg _) (hE i m)) (hP m)
  obtain ⟨C,D,hC,hD,hsolve⟩ := hall R hR q
  refine ⟨C,D,hC,hD,?_⟩
  intro G hG B hB hBρ hb τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall hp target
  have hbnd (i j) : L*E₀ i*B < r i j := by
    have hh := (lt_div_iff₀ (show 0 < 1+L*E₀ i by linarith [hL₀ i])).mp
      (hBρ.trans_le (hρr ⟨i,j⟩))
    nlinarith
  apply hsolve G hG (fun i _ => L*E₀ i*B)
    (fun i _ => mul_nonneg (hL₀ i) hB) hbnd _ τ ε η s hτ hs hτs hs1 hε hε1 hη hη1 hsmall _ target
  · intro i _
    have hh := (he₀ i (G-F) 1 B zero_lt_one le_rfl hB (hG.sub hF) hb).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    simp only [ContinuousLinearEquiv.coe_coe] at hh
    change WeightedEstimates.WeightedBound univ 1 2 _
      (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hh
    have hsub : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
        (spaceCoordinates ∘ A.vectorPlaneRead i G) -
          (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
      rw [A.vectorPlaneRead_sub]
      funext x
      exact map_sub spaceCoordinates _ _
    rw [hsub] at hh
    simpa only [L,mul_assoc] using hh
  · intro i m j hj
    have hh := (he i m G s (P m) hs hs1 (hP m) hG (hp m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    simpa only [R,L,mul_assoc,mul_div_assoc,ContinuousLinearEquiv.coe_coe] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
