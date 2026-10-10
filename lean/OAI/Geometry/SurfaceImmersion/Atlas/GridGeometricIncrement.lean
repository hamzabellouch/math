import OAI.Geometry.SurfaceImmersion.Atlas.GridAdjustedIncrement
import OAI.Geometry.SurfaceImmersion.Correction.GridMeanData
import OAI.Geometry.SurfaceImmersion.Correction.GridMeanBudgets
import OAI.Geometry.SurfaceImmersion.Atlas.GridCardinality
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

local instance gridGeometricIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGeometricIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridGeometricIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridGeometricIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridGeometricIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGeometricIncrementSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _


theorem grid_geometric_increment (g : SmoothMetric M) (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b a₀ C₀ H₀ K D : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH₀ : 0 ≤ H₀) (hK : 0 ≤ K) (hD : 0 < D)
:
    ∃ r : ℝ, 0 < r ∧ ∀ (FJ Y : ℕ → ℝ → ℝ),
    (∀ m, RealModes.HasPolynomialBound (FJ m)) →
    (∀ m, RealModes.HasPolynomialBound (Y m)) →
    (∀ m x, 1 ≤ x → 1 ≤ FJ m x) →
    (∀ m x, 1 ≤ x → 1 ≤ Y m x) → ∀ q : ℕ,
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, RealModes.HasPolynomialBound (P m)) ∧
      (∀ m, RealModes.HasPolynomialBound (Q m)) ∧
    ∀ z : ℝ, ∀ _hz : 0 < z, z ≤ 1 → ∀ a : A.centers → Finset Index,
      (∑ i, ((a i).card : ℝ)) ≤ K/z^12 →
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion (a i) (z^6)) →
    ∀ (Qb : ∀ i, (a i) → PhaseBasis)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ i k j, ξ (i,k.val,j) = (Qb i k).ξ j) → (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      (∀ i k j, ‖(Qb i k).Q j‖ ≤ C₀) →
      (∀ i k j y, (Qb i k).Q j (A.tensorPlaneRead i g.inner y) ≤ H₀) →
      (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        a₀ ≤ (Qb i k).Q j (A.tensorPlaneRead i g.inner y)) →
    ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a (z^6) l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a (z^6) κ ξ w F →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
      (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (w (i,k.val,j) • (Qb i k).ξ j) ∧
        ‖secondQuadratic (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (-(w (i,k.val,j) • (Qb i k).ξ j).2,(w (i,k.val,j) • (Qb i k).ξ j).1)‖⁻¹ ≤ D) →
    ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, 2*D ≤ FJ m z⁻¹ ∧ C₀ ≤ FJ m z⁻¹) →
      (∀ i k j m, ‖w (i,k.val,j) • (Qb i k).ξ j‖ ≤ FJ m z⁻¹ ∧
        ∀ hξ : w (i,k.val,j) • (Qb i k).ξ j ≠ 0,
          ‖(phaseEquiv (w (i,k.val,j) • (Qb i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ FJ m z⁻¹) →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (FJ m z⁻¹/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*(z⁻¹)^e))) →
    ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v v', f y v v' = f y v' v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m z⁻¹) f) →
    ∀ δ : ℝ, 0 < δ → δ ≤ τ →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • f)) := by
  classical
  obtain ⟨p,p',C,C',L,hC,hC',hL,r,ρ,R,hr,hρ,hR,hdata⟩ :=
    A.polynomial_grid_mean_data g ha₀ hC₀ hH₀
  refine ⟨r,hr,?_⟩
  intro FJ Y hFJ hY hFJ1 hY1 q
  let Cs := fun m x => C m*(FJ m x)^(p m)
  let Js := fun m x => 1+2*FJ m x
  let B := fun m x => 1+ρ⁻¹+gridMeanBudget p' C' L FJ m x
  let H := fun x => 1+ρ⁻¹+3*K*x^12
  have hCs (m : ℕ) : RealModes.HasPolynomialBound (Cs m) :=
    (RealModes.polynomialBound_const (zero_le_one.trans (hC m))).mul ((hFJ m).pow (p m))
  have hJs (m : ℕ) : RealModes.HasPolynomialBound (Js m) :=
    (RealModes.polynomialBound_const zero_le_one).add
      ((RealModes.polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul (hFJ m))
  have hB (m : ℕ) : RealModes.HasPolynomialBound (B m) :=
    ((RealModes.polynomialBound_const zero_le_one).add (RealModes.polynomialBound_const (inv_nonneg.mpr hρ.le))).add
      (gridMeanBudget_polynomial p' C' L FJ (fun m => zero_le_one.trans (hC' m))
        (fun m => zero_le_one.trans (hL m)) hFJ m)
  have hH : RealModes.HasPolynomialBound H :=
    ((RealModes.polynomialBound_const zero_le_one).add (RealModes.polynomialBound_const (inv_nonneg.mpr hρ.le))).add
      ((RealModes.polynomialBound_const (by positivity : 0 ≤ 3*K)).mul (RealModes.polynomialBound_id.pow 12))
  have hBn (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ gridMeanBudget p' C' L FJ m x :=
    (gridMeanBudget_polynomial p' C' L FJ (fun m => zero_le_one.trans (hC' m))
      (fun m => zero_le_one.trans (hL m)) hFJ m).nonneg hx
  have hB1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ B m x := by
    have hh := hBn m x hx
    have hi := inv_nonneg.mpr hρ.le
    dsimp [B]; linarith
  have hCs1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Cs m x :=
    one_le_mul_of_one_le_of_one_le (hC m) (one_le_pow₀ (hFJ1 m x hx))
  have hH1 (x : ℝ) (hx : 1 ≤ x) : 1 ≤ H x := by
    have hi := inv_nonneg.mpr hρ.le
    have hp : 0 ≤ 3*K*x^12 := by positivity
    dsimp [H]; linarith
  obtain ⟨e,E,P,Q,hE,hP,hQ,hstep⟩ := A.grid_adjusted_increment g V houter hε hκ hb
    FJ Cs Js B Y H hFJ hFJ1 hCs hJs hB hY hH hH1 hY1 hCs1 hB1 q
  refine ⟨e,E,P,Q,hE,hP,hQ,?_⟩
  intro z hz hz1 a hcard hcover Qb ξ w hξ hw hV hQnorm hQup hQlow F hF
    hlocal hpairs hImm hnormal hgram hcell τ s hτ hs hτs hs1 hBD hphases hFjets
    hsmall f hf hsym hnear hsize δ hδ hδτ
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr hz1
  let n := Fintype.card (A.GridPhaseIndex a)
  have hnH : (n : ℝ) ≤ H z⁻¹ := by
    change (Fintype.card (A.GridPhaseIndex a) : ℝ) ≤ _
    rw [A.gridPhaseIndex_card]
    have hc : 3*∑ i, ((a i).card : ℝ) ≤ 3*K*(z⁻¹)^12 := by
      have hh := mul_le_mul_of_nonneg_left hcard (by norm_num : (0:ℝ) ≤ 3)
      simpa only [inv_pow,div_eq_mul_inv,mul_assoc] using hh
    have hi := inv_nonneg.mpr hρ.le
    change 3*∑ i : A.centers, ((a i).card : ℝ) ≤ 1+ρ⁻¹+3*K*(z⁻¹)^12
    linarith
  have hgeom (i : A.centers) (k : a i) (j : Fin 3) (y : SmallModes.Base)
      (hy : y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base)) :=
    let hy' := (Set.image_mono (A.cellChartCompact_subset i (a i) (z^6) k.val)) hy
    And.intro (hImm i y hy') (And.intro (hcell i k j y hy).1
      (And.intro (hgram i y hy') (hcell i k j y hy).2))
  obtain ⟨c,d,hsolver,hcut,hform,hsupp,hbud⟩ := hdata z hz hz1 a hcover Qb
    (fun i k j => w (i,k.val,j)) (fun i k j => hw (i,k.val,j)) hQnorm hQup hQlow F hF τ s hs hs1
    D hD (fun m => FJ m z⁻¹) (fun m => hFJ1 m z⁻¹ hx) hBD hphases hFjets hgeom
  have hbud' (i : A.centers) (j : (a i) × Fin 3) (m : ℕ) :
      (d i j).budgets.inv m ≤ B m z⁻¹ ∧ (d i j).budgets.chi m ≤ B m z⁻¹ ∧
      (d i j).budgets.forms m ≤ B m z⁻¹ ∧ (d i j).budgets.pull m ≤ B m z⁻¹ ∧
      (d i j).budgets.psi m ≤ B m z⁻¹ ∧ (d i j).budgets.normal m ≤ B m z⁻¹ ∧
      (d i j).budgets.mode m ≤ B m z⁻¹ := by
    have he : linearMeanGeometryBudget p' C' (fun m => FJ m z⁻¹)
        (fun l => 1+phaseCutoffBudget l (L l/z^(6*l)) (FJ l z⁻¹) 1) m ≤ B m z⁻¹ := by
      rw [← gridMeanBudget_at_inverse]
      have hi := inv_nonneg.mpr hρ.le
      dsimp [B]; linarith
    obtain ⟨hi,hc,hf,hp,hψ,hn,hm⟩ := hbud i j m
    exact ⟨hi.trans he,hc.trans he,hf.trans he,hp.trans he,hψ.trans he,hn.trans he,hm.trans he⟩
  refine hstep (z^6) a ξ w hw hV n le_rfl z⁻¹ hx hnH r hr F hF
    hlocal hpairs hImm hnormal hgram d ?_ ?_ hρ hτ hs hτs hs1 ?_ ?_
    hbud' hFjets (pow_pos hz 6) hcover Qb ?_ ?_ ?_ ?_
    hsmall f hf hsym hnear hsize δ hδ hδτ
  · intro i j
    rw [hξ i j.1 j.2]
  · intro i j
    exact ⟨funext (fun m => (hsolver i j m).1),funext (fun m => (hsolver i j m).2.1),
      fun m => (hsolver i j m).2.2⟩
  · intro m
    have hh := hBn m z⁻¹ hx
    dsimp [B]; linarith
  · have hp : 0 ≤ 3*K*(z⁻¹)^12 := by positivity
    dsimp [H]; linarith
  · intro i k j
    funext y
    simp only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  · intro i k j y hy
    exact hcut i (k,j) y hy
  · intro i k j y _
    exact congrFun (hform i (k,j)) _
  · intro i k j
    change tsupport (fun y => A.planeWeight i y * normalizedCutoff (a i) (z^6) k.val y) ⊆ _
    exact hsupp i (k,j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
