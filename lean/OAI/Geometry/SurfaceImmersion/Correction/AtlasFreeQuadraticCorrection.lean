import OAI.Geometry.SurfaceImmersion.Geometry.UniformGlobalQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasAmplitudeReadBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasAmplitudeSupport

namespace OAI

/-! Construct a uniform forced correction for the actual atlas free oscillation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance freeQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance freeQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance freeQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance freeQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance freeQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance freeQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_free_quadratic_correction
    {n : A.centers → ℕ} {P : (k : A.centers) → Fin 3 → Fin (n k) → JetPolynomial.Expression}
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r r₀ : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 (r₀ i) ρ R (reference i))
    (c₀ : ∀ k l, PolynomialSolveData (P k) 0 (A.jetChartMap k F)
      (A.jetChartMap_smooth k hF)
      (A.globalQuadraticPhase (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) 1 1)
    (I : A.centers → RealModes.QuadraticLabel (A.centers × Fin 3) → ℕ → ℝ)
    (hI : ∀ k l m, 1 ≤ I k l m)
    (hi : ∀ k l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c₀ k l).e.target,
      ‖iteratedFDerivWithin ℝ j (c₀ k l).e.symm (c₀ k l).e.target x‖ ≤ I k l m)
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (q : ℕ) :
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ {τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ i, (d i).phase = (d₀ i).phase) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2 * Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2 * (τ/s)^(q+1) * Ct m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) + A.atlasFreeQuadraticOscillation d hρ δ q u)) := by
  classical
  let N := fun m => Finset.univ.sup
    (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q (m+1))
  choose a ha hamp using fun m =>
    A.uniform_atlas_amplitude_reads p hρ r reference q (m+1) (C (N m)) (hC (N m))
  obtain ⟨Cv,Ct,hCv,hCt,hcorr⟩ := A.uniform_global_quadratic_cancellation P F hF
    (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2)
    (fun a => A.freeGlobalPhase_smooth d₀ a.1 a.2)
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
    (fun a => isClosed_tsupport (A.weight a.1)) c₀ I hI hi a
    (fun m => zero_le_one.trans (ha m)) q
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro τ s d hfit hphase hτ hs hτs hs1 hK δ hδ u hu hball hbu
  let Z := fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2
  have hZ (a) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a) :=
    A.freeGlobalAmplitude_smooth d hρ δ q u a.1 a.2
  have hsp (a) : tsupport (Z a) ⊆ tsupport (A.weight a.1) :=
    A.freeGlobalAmplitude_tsupport d hρ δ q u hK a.1 a.2
  have hreads (k a₀ m) : WeightedEstimates.WeightedBound univ s (m+1)
      (a m*(δ*τ)) (A.vectorPlaneRead k (Z a₀)) :=
    hamp m d hfit hτ hs hτs hs1 δ hδ u hu hball (hbu (N m)) k a₀.1 a₀.2
  obtain ⟨W,hW,hsize,hres⟩ := hcorr τ δ s hτ hs hτs hs1 hδ Z hZ hsp hreads
  have hph (a : A.centers × Fin 3) : A.freeGlobalPhase d a.1 a.2 = A.freeGlobalPhase d₀ a.1 a.2 := by
    unfold freeGlobalPhase
    rw [hphase a.1]
  refine ⟨W,hW,hsize,?_⟩
  intro m
  rw [A.atlas_quadratic_oscillation_eq_global d hρ δ q u hK]
  simpa only [atlasGlobalNonzero,hph] using hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
