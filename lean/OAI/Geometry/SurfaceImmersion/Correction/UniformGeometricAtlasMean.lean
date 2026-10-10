import OAI.Geometry.SurfaceImmersion.Correction.UniformGeometricMeanFamily
import OAI.Geometry.SurfaceImmersion.Correction.UniformAtlasMean

namespace OAI

/-! Global charted mean data constructed from fixed unit-scale geometry.
The global trial radius is selected after the atlas amplification bound. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance geometricAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance geometricAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance geometricAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance geometricAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance geometricAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance geometricAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_geometric_atlas_mean
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : A.centers → Fin 3 → Base → ℝ} {K : A.centers → Fin 3 → TopologicalSpace.Compacts Base}
    (c₀ : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) 1 1)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (d₀ : ∀ i j, ChartedMeanData (c₀ i j) r₁ ρ R (A.tensorPlaneRead i reference)) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
      ∃ p : ∀ i, Fin 3 → ChartedMeanProfile (P i), ∃ β κ : ℕ → ℝ → ℝ,
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧
      ∀ (ε τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 →
      ∃ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) ∧
        (∀ i, (d i).G = G i ∧ (d i).phase = φ i ∧ (d i).support = K i ∧
          (∀ j, ((d i).solver j).e = (c₀ i j).e) ∧
          (∀ j x, ((d i).data j).cutoff x = (d₀ i j).cutoff x) ∧
          (∀ j, ((d i).data j).form = (d₀ i j).form)) ∧
        ∀ δ : ℝ, 0 < δ → MeanBounds univ s (A.tensorEncode reference) r L
          (rescaledMean (τ / s + ε / τ ^ loss)
            (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  classical
  choose p hp using fun i => unit_mean_family_uniform (c₀ i) (d₀ i)
  obtain ⟨D₀,hD₀,hall⟩ := A.uniform_atlas_mean_majorants_all_radii (R := R) p hρ reference href q
  have hDpos : 0 < D₀ := zero_lt_one.trans_le hD₀
  let r := r₁/(2*D₀)
  have hr : 0 < r := div_pos hr₁ (mul_pos (by norm_num) hDpos)
  have hDr : D₀*r = r₁/2 := by
    dsimp [r]
    field_simp
  have hsmallr : D₀*r ≤ r₁ := by rw [hDr]; linarith
  obtain ⟨hball,β,κ,hm⟩ := hall r hr.le
  refine ⟨r,D₀,hr,hD₀,hsmallr,p,β,κ,hball,?_⟩
  intro ε τ s hτ hs hτs hs1 hε hε1 hsmall
  choose d hd hmap hphase hsupport he hcut hform using fun i =>
    hp i ε τ s (D₀*r) hsmallr hτ hs hτs hs1 hε hε1
  refine ⟨d,hd,?_,?_⟩
  · exact fun i => ⟨hmap i,hphase i,hsupport i,he i,hcut i,hform i⟩
  · exact fun δ hδ => hm d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
