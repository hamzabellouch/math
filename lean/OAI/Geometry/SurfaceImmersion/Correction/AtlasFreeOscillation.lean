import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeFamily
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneCoordinates
import OAI.Geometry.SurfaceImmersion.Geometry.VectorPlaneRestore

namespace OAI

/-! The actual global free oscillation and its weighted displacement bound. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance atlasFreeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasFreeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasFreeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasFreeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasFreeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasFreeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def atlasFreeOscillation
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) : M → RealModes.RVec 4 :=
  A.vectorPlaneRestore (fun i => chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u))

omit [CompactSpace M] in
lemma atlasFreeOscillation_smooth
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ (A.atlasFreeOscillation d hρ δ q u) :=
  A.vectorPlaneRestore_smooth _ (fun i => (chartedFreeSum_smooth_support
    (d i).data hρ δ q (A.tensorPlaneRead i u)).1)

theorem uniform_atlas_free_size
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (q m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → τ/s + ε/τ^loss ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      A.TensorWeightedBound s N C u →
      A.WeightedBound τ m (B*(δ*τ)) (A.atlasFreeOscillation d hρ δ q u) := by
  classical
  dsimp only
  let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i
    (PolynomialSolveData.inputOrder (P := P i) q m)
  let C' := fun i => max 1 (D i*C)
  choose B E hB hE hfree using fun i : A.centers =>
    uniform_charted_free_family (R := R) (r := r i) (reference := reference i) (p i) hρ q m (C' i)
  let S := 1 + ∑ i : A.centers, B i
  have hS (i : A.centers) : B i ≤ S := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := B) (fun i _ => zero_le_one.trans (hB i)) (Finset.mem_univ i)
    change B i ≤ 1 + ∑ i : A.centers, B i
    linarith
  have hS0 : 0 ≤ S := by
    have hh : 0 ≤ ∑ i : A.centers, B i := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hB i))
    change 0 ≤ 1 + ∑ i : A.centers, B i
    linarith
  obtain ⟨D₀,hD₀,hrestore⟩ := A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  refine ⟨max 1 (D₀*S),le_max_left _ _,?_⟩
  intro ε τ s d hd hτ hs hτs hs1 hε hsmall δ hδ u hu hball hbu
  have hη (i : A.centers) : τ/s + ε/τ^tensorLoss (P i) ≤ 1 := by
    apply le_trans _ hsmall
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    apply pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
    exact Finset.le_sup (f := fun i : A.centers => tensorLoss (P i)) (Finset.mem_univ i)
  have hlocal (i : A.centers) : WeightedEstimates.WeightedBound univ s
      (PolynomialSolveData.inputOrder (P := P i) q m) (C' i) (A.tensorPlaneRead i u) := by
    have horder : PolynomialSolveData.inputOrder (P := P i) q m ≤ N := Finset.le_sup
      (f := fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
      (Finset.mem_univ i)
    have hbu' : A.TensorWeightedBound s (PolynomialSolveData.inputOrder (P := P i) q m) C u :=
      fun k => (hbu k).mono_order horder
    exact (hread i u s C hs hs1 hC hu hbu').mono_const (le_max_right _ _)
  have hsize (i : A.centers) : WeightedEstimates.WeightedBound univ τ m (S*(δ*τ))
      (chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)) := by
    have hh := (hfree i (d i).data (hd i) hτ hs hτs hs1 hε (hη i) δ hδ
      (A.tensorPlaneRead i u) (zero_le_one.trans (le_max_left _ _))
      (A.tensorPlaneRead_smooth i hu) (hball i) (hlocal i)).1
    exact hh.mono_const (mul_le_mul_of_nonneg_right (hS i) (mul_nonneg hδ hτ.le))
  have hh := hrestore _ τ (S*(δ*τ)) hτ (hτs.trans hs1)
    (mul_nonneg hS0 (mul_nonneg hδ hτ.le))
    (fun i => (chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).1) hsize
  intro i
  apply (hh i).mono_const
  calc
    D₀*(S*(δ*τ)) = (D₀*S)*(δ*τ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
