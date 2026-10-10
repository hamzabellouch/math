import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeRestore
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCubicRemainder
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasIncrementBound

namespace OAI

/-! The free/forced metric step for an arbitrary finite family of local phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance finiteIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance finiteIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance finiteIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance finiteIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteIncrementSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
local instance finiteIncrementIndexDecidable : DecidableEq (Σ i, ι i) := Classical.decEq _

def finiteAtlasFreeMean
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ∀ x : M, CovariantTwoTensor x :=
  δ^2 • A.tensorPlaneRestore (fun i => chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
    chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u))

noncomputable def finiteAtlasNonzero
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ∀ x : M, CovariantTwoTensor x := by
  classical
  exact A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
    (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
    (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x)

lemma finiteAtlasNonzero_smooth
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.finiteAtlasNonzero d hρ δ q u x)) := by
  classical
  apply A.tensorPlaneRestore_smooth
  intro k
  apply ((A.planeWeight_smooth k).pow 2).smul
  apply RealModes.contDiff_nonzeroPhaseSum
  · intro a
    exact A.vectorPlaneRead_smooth k (restore_smooth (a.1 : M) (A.outer_smooth a.1)
      (A.outer_support a.1) (c a.1 a.2).smoothPhase)
  · intro a
    exact A.vectorPlaneRead_smooth k (restore_smooth (a.1 : M) (A.outer_smooth a.1)
      (A.outer_support a.1) ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff)

lemma finite_atlas_metric_split
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
      A.finiteAtlasFreeMean d hρ δ q u + A.finiteAtlasNonzero d hρ δ q u :=
by
  simpa only [finiteAtlasFreeMean,finiteAtlasNonzero] using
    A.finite_atlas_free_metric d hρ hδ hτ q u hK

end SmoothingAtlas

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_atlas_increment_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
      (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
      (_hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
      (F V : M → Space), ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ V →
      ∀ H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      0 < τ → τ ≤ 1 → 0 < δ → δ ≤ τ → ∀ A₀ B₀ C₁ C₂ C₃ : ℝ,
      0 ≤ A₀ → 0 ≤ B₀ →
      let U := spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m C₁ (linearMetricTensor F U) →
      A.TensorWeightedBound τ m C₂ (linearMetricTensor F V + A.finiteAtlasNonzero d hρ δ q u) →
      A.TensorWeightedBound τ m C₃ (A.finiteAtlasFreeMean d hρ δ q u - δ^2 • H) →
      A.TensorWeightedBound τ m (C₁+C₂+C₃+D*(2*A₀*B₀+B₀^2)*(δ^3/τ))
        (inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H) := by
  obtain ⟨D,hD,hd⟩ := A.global_cubic_remainder_uniform_budget m
  refine ⟨D,hD,?_⟩
  intro ι _ n P G hG φ K τ s c r ρ R reference d hρ δ q u hK F V hF hV H hH hτ hτ1 hδ hδτ A₀ B₀ C₁ C₂ C₃ hA hB
  dsimp only
  intro hbU hbV h₁ h₂ h₃
  let U := spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u
  let T := A.finiteAtlasFreeMean d hρ δ q u
  let O := A.finiteAtlasNonzero d hρ δ q u
  have hU : ContMDiff planeModel spaceModel ∞ U :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (A.finiteAtlasFreeOscillation_smooth d hρ δ q u)
  have hO := A.finiteAtlasNonzero_smooth d hρ δ q u
  have hm : inducedTensor U = T+O := A.finite_atlas_metric_split d hρ hδ.ne' hτ.ne' q u hK
  have hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (T x)) := by
    have he : T = inducedTensor U-O := eq_sub_of_add_eq hm.symm
    rw [he]
    exact (A.inducedTensor_smooth hU).sub_section hO
  have hs₁ := A.linearMetricTensor_smooth hF hU
  have hs₂ := (A.linearMetricTensor_smooth hF hV).add_section hO
  have hs₃ := hT.sub_section (hH.const_smul_section (a := δ^2))
  have hs₄ := (A.linearMetricTensor_smooth hU hV).add_section (A.inducedTensor_smooth hV)
  have hout := A.tensorWeightedBound_add ((hs₁.add_section hs₂).add_section hs₃) hs₄ hτ.le
    (A.tensorWeightedBound_add (hs₁.add_section hs₂) hs₃ hτ.le
      (A.tensorWeightedBound_add hs₁ hs₂ hτ.le h₁ h₂) h₃)
    (hd A₀ B₀ hA hB τ δ hτ hτ1 hδ.le hδτ U V hU hV hbU hbV)
  have he : inducedTensor (F+(U+V))-inducedTensor F-δ^2 • H =
      (linearMetricTensor F U+(linearMetricTensor F V+O)+(T-δ^2 • H))+
        (linearMetricTensor U V+inducedTensor V) := by
    funext x
    ext v w
    have hmean := congrArg (fun t : ∀ x : M, CovariantTwoTensor x => t x v w) hm
    have hid := inducedForm_free_forced ((hF x).mdifferentiableAt (by simp))
      ((hU x).mdifferentiableAt (by simp)) ((hV x).mdifferentiableAt (by simp)) v w (δ^2*H x v w)
    change inducedForm (F+(U+V)) x v w-inducedForm F x v w-δ^2*H x v w =
      (linearMetricForm F U x v w+(linearMetricForm F V x v w+O x v w)+(T x v w-δ^2*H x v w))+
        (linearMetricForm U V x v w+inducedForm V x v w)
    change inducedForm U x v w=T x v w+O x v w at hmean
    linarith only [hid,hmean]
  rw [he]
  exact hout

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
