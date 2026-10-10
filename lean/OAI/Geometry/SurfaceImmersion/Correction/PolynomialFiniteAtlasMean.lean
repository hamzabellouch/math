import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetMeanFamily

namespace OAI

/-! Actual atlas mean bounds with polynomial dependence on all local budgets
and on the number of cells in each chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates FiniteMean
local instance polynomialFiniteMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFiniteMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFiniteMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFiniteMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialFiniteMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFiniteMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_finite_atlas_mean (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C D E : ℕ → ℝ),
      (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
    ∀ (reference : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (reference x)) →
    ∀ r : ℝ, 0 ≤ r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {ρ R : ℝ}
      (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ H B : ℕ → ℝ, (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ B m) →
      (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m ∧ ρ⁻¹ ≤ H m) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m ∧ (d i j).budgets.chi m ≤ B m ∧
        (d i j).budgets.forms m ≤ B m ∧ (d i j).budgets.pull m ≤ B m ∧
        (d i j).budgets.psi m ≤ B m ∧ (d i j).budgets.normal m ≤ B m ∧
        (d i j).budgets.mode m ≤ B m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds univ s (A.tensorEncode reference) r (q+2)
        (rescaledMean (τ/s) (A.tensorMeanOperator
          (A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q))))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
          (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
          (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E)) := by
  classical
  obtain ⟨p,C,hC,hmean⟩ := polynomial_mean_family_from_budgets q
  choose D hD hd using A.tensorPlaneRead_decode_bound
  choose E hE he using A.tensorPlaneRestore_bound
  refine ⟨p,C,D,E,hC,hD,hE,?_⟩
  intro reference href r hr ι _ n P G hG φ K τ s c ρ R d hρ hτ hs hτs hs1 H B hH hB hHB hb δ hδ
  have henv (m : ℕ) : 1 ≤ meanGeometryEnvelope q H B m := by
    dsimp [meanGeometryEnvelope]
    linarith [hH m,hB m,hB (m+q+2)]
  have hlocal (i : A.centers) := hmean (c i) (d i) hρ hτ hs hτs hs1 H B hH hB (hHB i) (hb i) δ hδ
  have hg := (A.atlasMean_polynomial_majorants reference href (q+2) p C
    (meanGeometryEnvelope q H B) hC henv D E hD hE hd he r hr).2 (s := (s : ℝ))
  have hη : 0 < τ/(s : ℝ) := div_pos hτ hs
  have hη1 : τ/(s : ℝ) ≤ 1 := (div_le_one₀ hs).mpr hτs
  apply hg hs hs1 (τ/s) hη (fun i => chartedFamilyMean (d i) hρ δ q)
  · intro i f hf hball
    have hh := (hlocal i).smooth (τ/s) hη hη1 f hf.contDiffOn hball
    rw [rescaledMean_self hη.ne'] at hh
    exact contDiffOn_univ.mp hh
  · intro i m C₀ f hC₀ hf hball hbf
    have hh := (hlocal i).value (τ/s) hη hη1 m C₀ f hC₀ hf.contDiffOn hball hbf
    rwa [rescaledMean_self hη.ne'] at hh
  · intro i m C₀ D₀ f g hC₀ hD₀ hf hg hballf hballg hbf hbg hdiff
    have hh := (hlocal i).difference (τ/s) hη hη1 m C₀ D₀ f g hC₀ hD₀
      hf.contDiffOn hg.contDiffOn hballf hballg hbf hbg hdiff
    rwa [rescaledMean_self hη.ne'] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
