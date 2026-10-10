import OAI.Geometry.SurfaceImmersion.Correction.GridFreeCorrection
import OAI.Geometry.SurfaceImmersion.Correction.GridGlobalQuadraticCorrection
import OAI.Geometry.SurfaceImmersion.Correction.GridFreeSupport
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAtlasFreeProfile
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds
import OAI.Geometry.SurfaceImmersion.Atlas.CatalogPhaseBounds
import OAI.Geometry.SurfaceImmersion.Atlas.FiniteAtlasIncrement

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridIncrementProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridIncrementProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridIncrementProfileDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridIncrementProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridIncrementProfileSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridIncrementProfileSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _


theorem grid_free_forced_increment (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J N B : ℕ → ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hN : ∀ m, RealModes.HasPolynomialBound (N m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ α β γ ζ : ℕ → ℝ → ℝ, ∃ D : ℕ → ℝ,
      (∀ m, RealModes.HasPolynomialBound (α m)) ∧
      (∀ m, RealModes.HasPolynomialBound (β m)) ∧
      (∀ m, RealModes.HasPolynomialBound (γ m)) ∧
      (∀ m, RealModes.HasPolynomialBound (ζ m)) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
        {τ : ℝ} {s : ℝ≥0}
        {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
          (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
          (A.cellChartCompact i (a i) h j.1.val) τ s}
        {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
        (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ H : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      ∀ Rm : ℕ → ℝ,
      (∀ m, A.TensorWeightedBound τ m (Rm m)
        (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • H)) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m
          ((α m x*(n : ℝ)+β m x*((n : ℝ)+2*(n : ℝ)^2))*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(ζ m x*(n : ℝ)*(δ*τ)+γ m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2)+Rm m+
            D m*(2*(α (m+1) x*(n : ℝ))*(β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))+
              (β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))^2)*(δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • H)) := by
  classical
  obtain ⟨Af,Rf,hAf,hRf,hfree⟩ := A.polynomial_atlas_free_profile q C J N B hC hJ hN hB hC1 hB1
  obtain ⟨e,E,hE,hquad⟩ := A.grid_free_quadratic_correction V houter hε hκ hb
    FJ C J N B hFJ hFJ1 hC hJ hN hB hC1 hB1 q
  choose D hD hinc using A.finite_atlas_increment_bound
  let L := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  let α := fun m x => L*Af m x
  let γ := fun m x => E m*x^(e m)
  let β := fun m x => L*γ m x
  have hL : 0 ≤ L := norm_nonneg _
  have hα (m : ℕ) : RealModes.HasPolynomialBound (α m) :=
    (RealModes.polynomialBound_const hL).mul (hAf m)
  have hγ (m : ℕ) : RealModes.HasPolynomialBound (γ m) :=
    (RealModes.polynomialBound_const (zero_le_one.trans (hE m))).mul
      (RealModes.polynomialBound_id.pow (e m))
  have hβ (m : ℕ) : RealModes.HasPolynomialBound (β m) :=
    (RealModes.polynomialBound_const hL).mul (hγ m)
  refine ⟨α,β,γ,Rf,D,hα,hβ,hγ,hRf,hD,?_⟩
  intro h a ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal hgram
    φ τ s c r ρ R reference d hφ hc hρ hτ hs hτs hs1 hρB hbud hFjets δ hδ hδτ u hu hball hbu
    H hH Rm hRm
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hK (i : A.centers) (j : (a i) × Fin 3) :
      (modeSupport (A.cellChartCompact i (a i) h j.1.val) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    Set.image_mono (A.cellChartCompact_subset i (a i) h j.1.val)
  have hcard (i : A.centers) : Fintype.card ((a i) × Fin 3) ≤ n :=
    (Fintype.card_le_of_injective (fun j : (a i) × Fin 3 => (⟨i,j⟩ : A.GridPhaseIndex a))
      (by intro j k he; exact eq_of_heq (Sigma.mk.inj he).2)).trans hn
  have hfr := hfree x hx n hcard F hF d hc hρ hτ hs hτs hs1 hK hρB hbud
    δ hδ.le u hu hball hbu
  obtain ⟨W,hW,hWb,hWe⟩ := hquad h a ξ w hw hV n hn x hx F hF hlocal hpairs
    hImm hnormal hgram d hφ hc hρ hτ hs hτs hs1 hρB hbud hFjets δ hδ.le u hu hball hbu
  let U₀ := spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u
  let V₀ := spaceCoordinates.symm ∘ W
  have hU₀ : ContMDiff planeModel spaceModel ∞ U₀ :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (A.finiteAtlasFreeOscillation_smooth d hρ δ q u)
  have hV₀ : ContMDiff planeModel spaceModel ∞ V₀ :=
    spaceCoordinates.symm.contDiff.contMDiff.comp hW
  have hUb (m : ℕ) : A.WeightedBound τ m (α m x*(n : ℝ)*(δ*τ)) U₀ := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap
      (A.finiteAtlasFreeOscillation_smooth d hρ δ q u) hτ.le (hfr m).1
    convert hh using 1
    · dsimp [α,L]
      ring
    · rfl
  have hVb (m : ℕ) : A.WeightedBound τ m
      (β m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2) V₀ := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hW hτ.le (hWb m)
    convert hh using 1
    · dsimp [β,γ,L]
      ring
    · rfl
  have hα0 (m : ℕ) : 0 ≤ α m x := by
    obtain ⟨_,_,_,hh⟩ := hα m
    exact (hh x hx).1
  have hβ0 (m : ℕ) : 0 ≤ β m x := by
    obtain ⟨_,_,_,hh⟩ := hβ m
    exact (hh x hx).1
  refine ⟨U₀+V₀,hU₀.add hV₀,?_,?_⟩
  · intro m
    have hδsq : δ^2 ≤ δ*τ := by nlinarith
    have hVb' : A.WeightedBound τ m
        (β m x*((n : ℝ)+2*(n : ℝ)^2)*(δ*τ)) V₀ :=
      fun i => (hVb m i).mono_const (mul_le_mul_of_nonneg_left hδsq (mul_nonneg (hβ0 m) (by positivity)))
    have hh := A.weightedBound_add hU₀ hV₀ hτ.le (hUb m) hVb'
    convert hh using 1
    ring
  · intro m
    have hh := hinc m d hρ δ q u hK F V₀ hF hV₀ H hH hτ hτ1 hδ hδτ
      (α (m+1) x*(n : ℝ)) (β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))
      ((τ/s)^(q+1)*(Rf m x*(n : ℝ)*(δ*τ)))
      ((τ/s)^(q+1)*(γ m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2)) (Rm m)
      (mul_nonneg (hα0 _) (Nat.cast_nonneg _)) (mul_nonneg (hβ0 _) (by positivity))
      (hUb (m+1)) (hVb (m+1)) (hfr m).2
      (by convert hWe m using 1; dsimp [γ]; ring) (hRm m)
    convert hh using 1
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
