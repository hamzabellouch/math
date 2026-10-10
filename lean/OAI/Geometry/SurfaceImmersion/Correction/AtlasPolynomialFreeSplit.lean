import OAI.Geometry.SurfaceImmersion.Correction.RestoredQuadratureMean
import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalFreeModes
import OAI.Geometry.SurfaceImmersion.Geometry.TensorRestoreFinite
import OAI.Geometry.SurfaceImmersion.Correction.UnperturbedMeanIdentity
import OAI.Geometry.SurfaceImmersion.Correction.RestoredPolynomialModeMean
import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalPolynomialMean
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLinearity
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeMetricSplit

namespace OAI

/-! The global finite phase expansion has the prescribed quadratic mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance polynomialFreeSplitFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFreeSplitFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFreeSplitDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFreeSplitDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialFreeSplitSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFreeSplitSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
attribute [local instance] Classical.propDecidable

theorem atlas_free_full_polynomial_split {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i))
    (hmap : ∀ i, (d i).G = A.jetChartMap i F)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
    inducedTensor U+A.atlasPolynomialQuadratic P ε F U =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u))+
      A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel (A.centers × Fin 3),
        QuadraticMean.displacement τ
          (coordinatePhase (A.globalQuadraticPhase
            (fun a : A.centers × Fin 3 => A.freeGlobalPhase d a.1 a.2) i l))
          (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ
            (fun a : A.centers × Fin 3 => A.freeGlobalPhase d a.1 a.2)
            (fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2)
            (fun a => A.freeGlobalPhase_smooth d a.1 a.2)
            (fun a => A.freeGlobalAmplitude_smooth d hρ δ q u a.1 a.2) i l) x) := by
  classical
  have hh := A.global_modes_full_quadratic P Q hQ hrep F hF ε τ
    (fun a : A.centers × Fin 3 => A.freeGlobalPhase d a.1 a.2)
    (fun a : A.centers × Fin 3 => A.freeGlobalAmplitude d hρ δ q u a.1 a.2)
    (fun a => A.freeGlobalPhase_smooth d a.1 a.2)
    (fun a => A.freeGlobalAmplitude_smooth d hρ δ q u a.1 a.2)
  have he : (∑ a : A.centers × Fin 3,
      surfaceMode τ (A.freeGlobalPhase d a.1 a.2) (A.freeGlobalAmplitude d hρ δ q u a.1 a.2)) =
      A.atlasFreeOscillation d hρ δ q u := by
    rw [Fintype.sum_prod_type]
    exact (A.atlas_free_global_modes d hρ δ q u hK).symm
  dsimp only at hh ⊢
  rw [he,A.atlas_global_polynomial_mean P Q hrep F hF d hmap hρ δ q u hK] at hh
  exact hh


/-- Exact error decomposition before estimating the mixed and cubic terms. -/
theorem polynomial_modes_free_forced_increment {n : A.centers → ℕ} {m : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F V : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (hV : ContMDiff planeModel spaceModel ∞ V) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    (T : ∀ p : M, CovariantTwoTensor p) :
    let U := spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)
    let O := A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
      QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
        (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x)
    A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T =
      (linearMetricTensor F U+A.atlasPolynomialVariation P ε F U)+
      (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+O)+
      (A.globalPolynomialQuadraticMean Q F ε τ φ Z-T)+
      ((inducedTensor (U+V)+A.atlasPolynomialQuadratic P ε F (U+V))-
        (inducedTensor U+A.atlasPolynomialQuadratic P ε F U))+
      A.atlasPolynomialRemainder P ε F (U+V) := by
  classical
  let U := spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)
  have hsum : ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞
      (∑ j, surfaceMode τ (φ j) (Z j)) := by
    convert ContMDiff.sum (t := Finset.univ) (fun j _ => surfaceMode_smooth τ (hφ j) (hZ j)) using 1
    funext p
    simp only [Finset.sum_apply]
  have hU : ContMDiff planeModel spaceModel ∞ U :=
    spaceCoordinates.symm.contDiff.contMDiff.comp hsum
  have he := A.global_modes_full_quadratic P Q hQ hrep F hF ε τ φ Z hφ hZ
  dsimp only at he ⊢
  have ht := A.atlas_polynomial_metric_taylor_identity P ε hF (hU.add hV)
  have hl := A.atlasPolynomialVariation_add P ε F hU hV
  have hm : linearMetricTensor F (U+V) = linearMetricTensor F U+linearMetricTensor F V := by
    have hh := linearMetricTensor_finite_sum F ![U,V] (by
      intro j
      fin_cases j
      · exact hU
      · exact hV)
    convert hh using 1
    · simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    · funext p
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.add_apply]
  rw [ht,hl,hm]
  change _ = _
  rw [he]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
