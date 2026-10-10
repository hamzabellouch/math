import OAI.Geometry.SurfaceImmersion.Correction.UniformAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorFiniteMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorSymmetricMean
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasQuadraticResidual

namespace OAI

/-! Uniform finite mean adjustment from profiles, including varying base maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation
local instance profiledMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance profiledMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance profiledMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem profiled_atlas_adjusted_mean
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i))
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
      ∃ β κ : ℕ → ℝ → ℝ,
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) → ∀ steps : ℕ,
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ (ε τ : ℝ), 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ/s + ε/τ^loss ≤ η₀ →
      ∀ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) →
        (∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j)) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
        (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
      ∀ δ : ℝ, 0 < δ → ∀ j ≤ steps, ∃ u : ∀ x : M, CovariantTwoTensor x,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (u x)) ∧
        (∀ x v v', u x v v' = u x v' v) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
        (∀ i, InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) (A.tensorPlaneRead i u)) ∧
        (∀ m, A.TensorWeightedBound s m (sizeBound L C β j m) u) ∧
        (∀ m, A.TensorWeightedBound s m
          (δ^2 * (differenceBound L C β κ j m * (τ/s + ε/τ^loss)^(j+1)))
          (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) := by
  obtain ⟨D₀,hD₀,hall⟩ := A.uniform_atlas_mean_majorants_all_radii (R := R) p hρ reference href q
  have hDpos : 0 < D₀ := zero_lt_one.trans_le hD₀
  let r := r₁/(2*D₀)
  have hr : 0 < r := div_pos hr₁ (mul_pos (by norm_num) hDpos)
  have hDr : D₀*r = r₁/2 := by dsimp [r]; field_simp
  obtain ⟨hball,β,κ,hm⟩ := hall r hr.le
  refine ⟨r,D₀,hr,hD₀,?_,β,κ,?_⟩
  · rw [hDr]
    linarith
  · intro C hC steps
    obtain ⟨η₀,hη₀,hη₁,htall⟩ := A.tensor_finite_mean_substitution_uniform
      (by linarith : r/2 < r) hC steps (B := β) (K := κ)
    refine ⟨η₀,hη₀,hη₁,?_⟩
    intro s hs hs1 H hH hsym hH0 hHC ε τ hτ hτs hε hε1 hsmall d hfit hphase hcut hform hsup δ hδ j hj
    have hη : 0 < τ/s + ε/τ^(Finset.univ.sup (fun i : A.centers => tensorLoss (P i))) :=
      add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
    obtain ⟨hu,hb,hsize,herror⟩ := htall s hs reference H hH hH0 hHC _ hη hsmall _
      (hm d hfit hτ hs hτs hs1 hε hε1 (hsmall.trans hη₁) δ hδ) j hj
    have hsymu := A.tensorMeanTrial_symmetric H (A.atlasMean (fun i => (d i).mean hρ δ q)) hsym
      (fun u _ => A.atlasMean_symmetric _ u) j
    have hlocal (i : A.centers) := hball _ (A.tensorEncode_smooth hu) hb i
    simp only [A.tensorDecode_encode] at hlocal
    refine ⟨_,hu,hsymu,hb,hlocal,hsize,?_⟩
    intro m
    exact A.charted_family_atlas_quadratic_residual d hρ Q w hw hphase hcut hform hsup
      _ H hu hH hsymu hlocal hδ.ne' hτ.ne' q (herror m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
