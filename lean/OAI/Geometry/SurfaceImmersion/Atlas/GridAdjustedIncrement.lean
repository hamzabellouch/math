import OAI.Geometry.SurfaceImmersion.Primitive.GridIncrementProfile
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFiniteAtlasTrial
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialTensorReadBudget
import OAI.Geometry.SurfaceImmersion.Correction.GridFreeMeanIdentity
import OAI.Geometry.SurfaceImmersion.Atlas.GridIncrementEnvelope
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

local instance gridAdjustedIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridAdjustedIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridAdjustedIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridAdjustedIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridAdjustedIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridAdjustedIncrementSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _


theorem grid_adjusted_increment (g : SmoothMetric M) (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J B Y : ℕ → ℝ → ℝ) (H : ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hY : ∀ m, RealModes.HasPolynomialBound (Y m)) (hH : RealModes.HasPolynomialBound H)
    (hH1 : ∀ x, 1 ≤ x → 1 ≤ H x) (hY1 : ∀ m x, 1 ≤ x → 1 ≤ Y m x)
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, RealModes.HasPolynomialBound (P m)) ∧
      (∀ m, RealModes.HasPolynomialBound (Q m)) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x → (n : ℝ) ≤ H x → ∀ r : ℝ, 0 < r →
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
        {ρ R : ℝ}
        (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i g.inner)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ _hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      ρ⁻¹ ≤ H x →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.chi m ≤ B m x ∧
        (d i j).budgets.forms m ≤ B m x ∧ (d i j).budgets.pull m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ B m x ∧
        (d i j).budgets.mode m ≤ B m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      (hh : 0 < h) →
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion (a i) h) →
      ∀ Qb : ∀ i, (a i) → PhaseBasis,
      (∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w (i,k.val,j) • (Qb i k).ξ j)) →
      (∀ i k j y, y ∈ (c i (k,j)).e.source → (d i (k,j)).cutoff ((c i (k,j)).e y) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val y / w (i,k.val,j)) →
      (∀ i k j y, y ∈ (c i (k,j)).e.source →
        (d i (k,j)).form ((c i (k,j)).e y) = (Qb i k).Q j) →
      (∀ i k j, tsupport (supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆
        (c i (k,j)).e.source) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*x^e))) →
      ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v v', f y v v' = f y v' v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m x) f) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m x*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m x*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • f)) := by
  classical
  obtain ⟨e,E,S,T,hE,hS,hT,htrial⟩ :=
    A.polynomial_finite_atlas_trial q B (fun _ => H) Y hB (fun _ => hH) hY
  obtain ⟨Rb,hRb,hRb1,hread⟩ := A.polynomial_tensor_read_budget S hS
  let B' := fun m x => 1+B m x+Rb m x
  have hB' (m : ℕ) : RealModes.HasPolynomialBound (B' m) :=
    ((RealModes.polynomialBound_const zero_le_one).add (hB m)).add (hRb m)
  have hB'1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ B' m x := by
    have hb := hB1 m x hx
    have hr := (hRb1 m x hx).1
    dsimp [B']; linarith
  have hBB' (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : B m x ≤ B' m x := by
    have hr := (hRb1 m x hx).1
    dsimp [B']; linarith
  have hRB' (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : Rb m x ≤ B' m x := by
    have hb := hB1 m x hx
    dsimp [B']; linarith
  obtain ⟨α,β,γ,ζ,D,hα,hβ,hγ,hζ,hD,hinc⟩ := A.grid_free_forced_increment V houter hε hκ hb
    FJ C J B B' hFJ hFJ1 hC hJ hB hB' hC1 hB'1 q
  let P := gridIncrementSize α β H
  let Q := gridIncrementError α β γ ζ T D H
  refine ⟨e,E,P,Q,hE,gridIncrementSize_polynomial α β H hα hβ hH,
    gridIncrementError_polynomial α β γ ζ T D H hα hβ hγ hζ hT hD hH,?_⟩
  intro h a ξ w hw hV n hn x hx hnH r hr F hF hlocal hpairs hImm hnormal hgram
    φ τ s c ρ R d hφ hc hρ hτ hs hτs hs1 hρB hρH hbud hFjets hh hcover Qb hphase
    hcut hform hsup hsmall f hf hsym hnear hsize δ hδ hδτ
  have hK (i : A.centers) (j : (a i) × Fin 3) :
      (modeSupport (A.cellChartCompact i (a i) h j.1.val) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    Set.image_mono (A.cellChartCompact_subset i (a i) h j.1.val)
  have hcard (i : A.centers) : (Fintype.card ((a i) × Fin 3) : ℝ) ≤ H x := by
    have hi : Fintype.card ((a i) × Fin 3) ≤ n :=
      (Fintype.card_le_of_injective (fun j : (a i) × Fin 3 => (⟨i,j⟩ : A.GridPhaseIndex a))
        (by intro j k he; exact eq_of_heq (Sigma.mk.inj he).2)).trans hn
    exact (Nat.cast_le.mpr hi).trans hnH
  obtain ⟨u,hu,husym,_,huball,husize,hures⟩ := htrial x hx g.inner g.contMDiff r hr d hρ
    hτ hs hτs hs1 (fun _ => hH1 x hx) (fun m => hY1 m x hx)
    (fun i _ => ⟨hcard i,hρH⟩) hbud hsmall f hf hsym hnear hsize δ hδ
  have hub (i : A.centers) (m : ℕ) := hread x hx s hs hs1 u hu husize i m
  have hbud' (i : A.centers) (j : (a i) × Fin 3) (m : ℕ) :
      (d i j).budgets.inv m ≤ B' m x ∧ (d i j).budgets.forms m ≤ B' m x ∧
      (d i j).budgets.psi m ≤ B' m x ∧ (d i j).budgets.normal m ≤ B m x :=
    ⟨(hbud i j m).1.trans (hBB' m x hx),
      (hbud i j m).2.2.1.trans (hBB' m x hx),
      (hbud i j m).2.2.2.2.1.trans (hBB' m x hx),(hbud i j m).2.2.2.2.2.1⟩
  have hmean (m : ℕ) : A.TensorWeightedBound τ m (δ^2*T m x*(τ/s)^(q+1))
      (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • f) := by
    have he := A.grid_free_mean_residual hh hcover d hρ Qb (fun i k j => w (i,k.val,j))
      (fun i k j => (zero_lt_one.trans_le (hw (i,k.val,j))).ne') hphase hcut hform hsup hK
      u hu husym huball hδ.ne' hτ.ne' q f hf hτ hτs (hures m)
    convert he using 1
    ring
  obtain ⟨U,hU,hUb,hUe⟩ := hinc h a ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal
    hgram d hφ hc hρ hτ hs hτs hs1 (fun m => (hρB m).trans (hBB' m x hx)) hbud' hFjets
    δ hδ hδτ u hu huball (fun i m => (hub i m).mono_const (hRB' m x hx)) f hf
    (fun m => δ^2*T m x*(τ/s)^(q+1)) hmean
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnon (Z : ℕ → ℝ → ℝ) (hz : ∀ m, RealModes.HasPolynomialBound (Z m)) (m : ℕ) :
      0 ≤ Z m x := by obtain ⟨_,_,_,hp⟩ := hz m; exact (hp x hx).1
  refine ⟨U,hU,?_,?_⟩
  · intro m i
    apply (hUb m i).mono_const
    exact gridIncrementSize_bound (hnon α hα m) (hnon β hβ m) hn0 hnH hδ.le hτ.le
  · intro m i
    apply (hUe m i).mono_const
    exact gridIncrementError_bound (hnon α hα (m+1)) (hnon β hβ (m+1))
      (hnon γ hγ m) (hnon ζ hζ m) (hnon T hT m) (hD m) hn0 hnH hδ.le hτ hδτ
      (hτs.trans hs1) (pow_nonneg (div_nonneg hτ.le hs.le) _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
