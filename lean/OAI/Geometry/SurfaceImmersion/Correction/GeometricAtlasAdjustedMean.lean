import OAI.Geometry.SurfaceImmersion.Correction.UniformGeometricAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorFiniteMean
import OAI.Geometry.SurfaceImmersion.Correction.TensorSymmetricMean
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasQuadraticResidual

namespace OAI

/-! Finite adjustment of the actual global quadratic mean, starting from
fixed unit-scale geometric data and constructing all later local solvers. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance geometricAdjustedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance geometricAdjustedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance geometricAdjustedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance geometricAdjustedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance geometricAdjustedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance geometricAdjustedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem geometric_atlas_adjusted_mean
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : A.centers → Fin 3 → Base → ℝ} {K : A.centers → Fin 3 → TopologicalSpace.Compacts Base}
    (c₀ : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) 1 1)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (d₀ : ∀ i j, ChartedMeanData (c₀ i j) r₁ ρ R (A.tensorPlaneRead i reference))
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase₀ : ∀ i j, coordinatePhase (φ i j) = phaseLinear (w i j • (Q i).ξ j))
    (hcut₀ : ∀ i j x, x ∈ (c₀ i j).e.source →
      (d₀ i j).cutoff ((c₀ i j).e x) = A.planeWeight i x / w i j)
    (hform₀ : ∀ i j x, x ∈ (c₀ i j).e.source → (d₀ i j).form ((c₀ i j).e x) = (Q i).Q j)
    (hsup₀ : ∀ i j, tsupport (A.planeWeight i) ⊆ (c₀ i j).e.source) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧
      ∃ p : ∀ i, Fin 3 → ChartedMeanProfile (P i), ∃ β κ : ℕ → ℝ → ℝ,
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) → (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ steps : ℕ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (ε τ : ℝ), 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ/s + ε/τ^loss ≤ η₀ →
      ∃ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) ∧
        (∀ i, (d i).G = G i ∧ (d i).phase = φ i ∧ (d i).support = K i) ∧
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
  obtain ⟨r,D₀,hr,hD₀,_,p,β,κ,hball,hbuild⟩ :=
    A.uniform_geometric_atlas_mean c₀ hr₁ hρ reference href d₀ q
  refine ⟨r,D₀,hr,hD₀,p,β,κ,?_⟩
  intro s hs hs1 H hH hsym hH0 C hC hHC steps
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := A.tensor_finite_mean_substitution hs (by linarith : r/2 < r)
    hC hH hH0 hHC steps (B := β) (K := κ)
  refine ⟨η₀,hη₀,hη₁,?_⟩
  intro ε τ hτ hτs hε hε1 hsmall
  have hη : 0 < τ/s + ε/τ^(Finset.univ.sup (fun i : A.centers => tensorLoss (P i))) :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨d,hfit,hgeom,hm⟩ := hbuild ε τ s hτ hs hτs hs1 hε hε1 (hsmall.trans hη₁)
  have hphase (i : A.centers) (j : Fin 3) :
      coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j) := by
    rw [(hgeom i).2.1]
    exact hphase₀ i j
  have hcut (i : A.centers) (j : Fin 3) (x : SmallModes.Base)
      (hx : x ∈ ((d i).solver j).e.source) :
      ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j := by
    obtain ⟨_,_,_,he,hc,_⟩ := hgeom i
    rw [hc j _,he j]
    exact hcut₀ i j x (by simpa only [he j] using hx)
  have hform (i : A.centers) (j : Fin 3) (x : SmallModes.Base)
      (hx : x ∈ ((d i).solver j).e.source) :
      ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j := by
    obtain ⟨_,_,_,he,_,hf⟩ := hgeom i
    rw [hf j,he j]
    exact hform₀ i j x (by simpa only [he j] using hx)
  have hsup (i : A.centers) (j : Fin 3) : tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source := by
    obtain ⟨_,_,_,he,_,_⟩ := hgeom i
    rw [he j]
    exact hsup₀ i j
  refine ⟨d,hfit,(fun i => ⟨(hgeom i).1,(hgeom i).2.1,(hgeom i).2.2.1⟩),?_⟩
  intro δ hδ j hj
  obtain ⟨hu,hb,hsize,herror⟩ := ht _ hη hsmall _ (hm δ hδ) j hj
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
