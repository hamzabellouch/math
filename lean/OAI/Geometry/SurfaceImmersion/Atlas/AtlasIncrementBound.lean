import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasIncrementIdentity
import OAI.Geometry.SurfaceImmersion.Correction.UnperturbedMeanIdentity
import OAI.Geometry.Immersion.ClosedSurface.FiniteIncrement

namespace OAI

/-! Quantitative assembly of the actual global free/forced metric increment. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData
open PhaseMean
lemma unperturbed_quadraticMean_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {τ : ℝ} {s : ℝ≥0} {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanFamilyData P 0 τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.quadraticMean hρ δ q f) := by
  rw [d.quadraticMean_unperturbed]
  exact RealModes.contDiff_zeroPhaseSum
    (fun j => (d.solver j).smoothPhase.comp planeCoordinateIsometry.symm.contDiff)
    (fun j => ((d.data j).freeAmplitude hρ δ q f).contDiff.comp planeCoordinateIsometry.symm.contDiff) τ
end ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance incrementBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance incrementBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance incrementBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance incrementBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance incrementBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance incrementBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_free_forced_increment_bound (m : ℕ) (A₀ B₀ : ℝ) (hA : 0 ≤ A₀) (hB : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : A.centers → ℕ}
      {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
      {τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
      {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
      (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
      (_hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
      (F V : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
      (_hV : ContMDiff planeModel spaceModel ∞ V) (H : ∀ x : M, CovariantTwoTensor x)
      (_hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p))),
      0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ → ∀ C₁ C₂ C₃ : ℝ,
      let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m C₁ (linearMetricTensor F U) →
      A.TensorWeightedBound τ m C₂ (linearMetricTensor F V + A.atlasFreeQuadraticOscillation d hρ δ q u) →
      A.TensorWeightedBound τ m C₃
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) →
      A.TensorWeightedBound τ m (C₁+C₂+C₃+D*(δ^3/τ))
        (inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H) := by
  obtain ⟨D,hD,hd⟩ := A.global_cubic_remainder_bound m A₀ B₀ hA hB
  refine ⟨D,hD,?_⟩
  intro n P τ s r ρ R reference d hρ δ q u hK F V hF hV H hH hτ hτ1 hδ hδτ C₁ C₂ C₃
  dsimp only
  intro hbU hbV h₁ h₂ h₃
  let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
  have hU : ContMDiff planeModel spaceModel ∞ U :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (A.atlasFreeOscillation_smooth d hρ δ q u)
  let T := A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u))
  have hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)) :=
    A.tensorPlaneRestore_smooth (fun i => (d i).unperturbed_quadraticMean_smooth hρ δ q _)
  have hosceq : A.atlasFreeQuadraticOscillation d hρ δ q u = inducedTensor U - T := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact (A.atlas_free_metric_split d hρ δ q u hK).symm
  have hosc : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasFreeQuadraticOscillation d hρ δ q u p)) := by
    rw [hosceq]
    exact (A.inducedTensor_smooth hU).sub_section hT
  have hs₁ := A.linearMetricTensor_smooth hF hU
  have hs₂ := (A.linearMetricTensor_smooth hF hV).add_section hosc
  have hs₃ := hT.sub_section (hH.const_smul_section (a := δ^2))
  have hs₄ := (A.linearMetricTensor_smooth hU hV).add_section (A.inducedTensor_smooth hV)
  have hh := A.tensorWeightedBound_add ((hs₁.add_section hs₂).add_section hs₃) hs₄ hτ.le
    (A.tensorWeightedBound_add (hs₁.add_section hs₂) hs₃ hτ.le
      (A.tensorWeightedBound_add hs₁ hs₂ hτ.le h₁ h₂) h₃)
    (hd τ δ hτ hτ1 hδ hδτ U V hU hV hbU hbV)
  have herr : inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H =
      (linearMetricTensor F U +
        (linearMetricTensor F V + A.atlasFreeQuadraticOscillation d hρ δ q u) +
        (T - δ^2 • H)) + (linearMetricTensor U V + inducedTensor V) := by
    calc
      _ = linearMetricTensor F U +
          (linearMetricTensor F V + A.atlasFreeQuadraticOscillation d hρ δ q u) +
          (T - δ^2 • H) + linearMetricTensor U V + inducedTensor V :=
        A.atlas_free_forced_increment d hρ δ q u hK hF hV H
      _ = _ := by rw [add_assoc]
  change A.TensorWeightedBound τ m _ (inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H)
  rw [herr]
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
