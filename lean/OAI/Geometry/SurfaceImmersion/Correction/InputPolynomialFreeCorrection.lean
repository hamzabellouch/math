import OAI.Geometry.SurfaceImmersion.Correction.InputPolynomialQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialAmplitudeBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalPolynomialMean
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasAmplitudeSupport

namespace OAI

/-! Construct a forced correction uniformly for nearby maps from their input norms. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance inputPolynomialFreeQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPolynomialFreeQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputPolynomialFreeQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputPolynomialFreeQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputPolynomialFreeQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputPolynomialFreeQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem input_polynomial_free_correction_fixed_phase
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : A.centers × Fin 3 → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          φ k l)) x))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ∀ i, Fin 3 → ChartedMeanProfile (Q i)) {ρ R : ℝ} (hρ : 0 < ρ),
      ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
      (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
    (C : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (q : ℕ),
    ∃ Cv Ct : ℕ → ℝ,
      (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ B : ℝ,
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
      ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 < δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2 * Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2 * η^(q+1) * Ct m)
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            (inducedTensor (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u) +
              A.atlasPolynomialQuadratic Pol ε G (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u) -
              A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u))))) := by
  classical
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_global_polynomial_quadratic_cancellation_all_profiles Pol Q hQ hquad hlin F hF φ hφ
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
    (fun a => isClosed_tsupport (A.weight a.1)) hImm hgood U hU KU hUK hweight
  refine ⟨ρ₀,hρ₀,?_⟩
  intro p ρ R hρ r reference D hD C hC q
  let N := fun m => Finset.univ.sup
    (fun i : A.centers => PolynomialSolveData.inputOrder (P := Q i) q (m+1))
  choose a ha hamp using fun m =>
    A.uniform_polynomial_atlas_amplitude_reads p hρ r reference q (m+1) (C (N m)) (hC (N m))
  obtain ⟨Cv,Ct,hCv,hCt,hcorr⟩ := hall D a hD
    (fun m => zero_le_one.trans (ha m)) q
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb ε τ s d hfit hphase hdG hτ hs hτs hs1 hε hε1 η hη hη1 hsmall hd hK δ hδ u hu hball hbu
  let Z := fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2
  have hZ (a) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a) :=
    A.freeGlobalAmplitude_smooth d hρ δ q u a.1 a.2
  have hsp (a) : tsupport (Z a) ⊆ tsupport (A.weight a.1) :=
    A.freeGlobalAmplitude_tsupport d hρ δ q u hK a.1 a.2
  have hreads (k a₀ m) : WeightedEstimates.WeightedBound univ s (m+1)
      (a m*(δ*τ)) (A.vectorPlaneRead k (Z a₀)) :=
    hamp m d hfit hτ hs hτs hs1 hε (fun i => (hsmall i).trans hη1) δ hδ.le u hu hball (hbu (N m)) k a₀.1 a₀.2
  obtain ⟨W,hW,hsize,hres⟩ := hcorr G hG B hB hBρ hb τ δ ε η s hτ hs hτs hs1 hδ hε hε1 hη hη1 hsmall hd Z hZ hsp hreads
  have hph (i : A.centers) (j : Fin 3) : A.freeGlobalPhase d i j = φ (i,j) := hphase (i,j)
  have hmode : (∑ a : A.centers × Fin 3, surfaceMode τ (φ a) (Z a)) =
      A.atlasFreeOscillation d hρ δ q u := by
    rw [Fintype.sum_prod_type]
    simpa only [Z,hph] using (A.atlas_free_global_modes d hρ δ q u hK).symm
  have hmean : A.globalPolynomialQuadraticMean Q G ε τ φ Z =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) := by
    have hh := A.atlas_global_polynomial_mean Pol Q hquad G hG d hdG hρ δ q u hK
    simpa only [hphase,Z] using hh
  refine ⟨W,hW,hsize,?_⟩
  intro m
  simpa only [hmode,hmean] using hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
