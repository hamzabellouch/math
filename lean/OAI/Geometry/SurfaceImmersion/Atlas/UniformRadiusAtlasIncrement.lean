import OAI.Geometry.SurfaceImmersion.Correction.FixedBallProfiledAtlasMean
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedAtlasPhases
import OAI.Geometry.SurfaceImmersion.Atlas.InputAtlasSmallIncrement
import OAI.Geometry.SurfaceImmersion.Correction.UniformAtlasPhaseMeanData

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance uniformRadiusAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformRadiusAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformRadiusAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformRadiusAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformRadiusAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformRadiusAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_radius_atlas_increment
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (hsupport : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i)
    (hSU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hmargin : ∀ i j x, x ∈ U i j →
      ρ + ‖(Q i).Q j‖*r₁ ≤ (Q i).Q j (A.tensorPlaneRead i reference x) ∧
      (Q i).Q j (A.tensorPlaneRead i reference x) ≤ R - ‖(Q i).Q j‖*r₁)
    (hImmQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgoodQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x))
    : ∃ r ρ₀ : ℝ, 0 < r ∧ 0 < ρ₀ ∧
      ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) → ∀ q : ℕ,
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (η₀ : ℝ) (B T : ℕ → ℝ), 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ : ℝ, 0 < τ → τ ≤ s → τ/s ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (G+X) - inducedTensor G - δ^2 • H)) := by
  classical
  obtain ⟨ρd,hρd,halldata⟩ := A.uniform_atlas_phase_mean_data_all_profiles F hF Q w hw Ω U K
    hΩ hU hK hUK hKΩ hImm hgood hsupport U₀ hU₀ K₀ hU₀K hSU₀
    (fun i => A.tensorPlaneRead i reference) hmargin
  obtain ⟨ρs,hρs,hallsmall⟩ := A.input_atlas_small_increment_fixed_phase F hF
    (A.linearAtlasPhase Q w) (A.linearAtlasPhase_smooth Q w) hImmQ hgoodQ
  let r := A.tensorTrialRadius r₁
  let D₀ := A.tensorReadBallConstant
  have hr : 0 < r := A.tensorTrialRadius_pos hr₁
  have hDr : D₀*r ≤ r₁ := A.tensorTrialRadius_margin hr₁.le
  refine ⟨r,min ρd ρs,hr,lt_min hρd hρs,?_⟩
  intro P hP q C hC
  obtain ⟨p,hdata⟩ := halldata P hP
  obtain ⟨_,_,_,β,κ,hmean⟩ := A.profiled_atlas_adjusted_mean_fixed_ball
    p hr₁ hρ reference href Q w hw q
  let L := Finset.univ.sup (fun _ : A.centers =>
    tensorOrder emptyMetricPolynomial+1+(q+1)*(tensorOrder emptyMetricPolynomial+1))
  let Cu := fun m => max 1 (sizeBound L C β q m)
  let E := fun m => max 1 (differenceBound L C β κ q m)
  have hCu (m : ℕ) : 0 ≤ Cu m := zero_le_one.trans (le_max_left _ _)
  have hE (m : ℕ) : 0 ≤ E m := zero_le_one.trans (le_max_left _ _)
  obtain ⟨B,T,hB,hT,hsmall⟩ := hallsmall p hρ (fun _ => D₀*r)
    (fun i => A.tensorPlaneRead i reference) P hP Cu E hCu hE q
  obtain ⟨η₀,hη₀,hη₁,hmeanUniform⟩ := hmean C hC q
  refine ⟨η₀,B,T,hη₀,hη₁,hB,hT,?_⟩
  intro G hG b hb hbρ hclose s hs hs1 hp H hH hsym hnear hbC τ δ hτ hτs hη hδ hδτ
  obtain ⟨d,hfit,hmap,hphase,hsupport',hlinear,hcut,hform,hsup⟩ :=
    hdata G hG b hb (hbρ.trans_le (min_le_left _ _)) hclose s hs hs1 hp τ (D₀*r) hDr
  have hphaseGlobal (a : A.centers × Fin 3) :
      A.freeGlobalPhase d a.1 a.2 = A.linearAtlasPhase Q w a := by
    unfold freeGlobalPhase linearAtlasPhase
    rw [hphase a.1]
  have hK' (i j) : (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    rw [hsupport' i]
  obtain ⟨u,hu,_,_,hball,hsize,herror⟩ := hmeanUniform s hs hs1 H hH hsym hnear hbC
    0 τ hτ hτs (le_refl 0) (by norm_num)
    (by simpa only [zero_div,add_zero] using hη) d hfit hlinear hcut hform hsup δ hδ q le_rfl
  have hbu (m) : A.TensorWeightedBound s m (Cu m) u :=
    fun i => (hsize m i).mono_const (le_max_right _ _)
  have hmu (m) : A.TensorWeightedBound τ m (E m*δ^2*(τ/s)^(q+1))
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
    intro i
    have hh := (herror m i).shrink_scale hτ.le hτs
    simp only [zero_div,add_zero] at hh
    apply hh.mono_const
    calc
      δ^2*(differenceBound L C β κ q m*(τ/s)^(q+1)) ≤
          δ^2*(E m*(τ/s)^(q+1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (pow_nonneg (div_nonneg hτ.le hs.le) _)) (sq_nonneg δ)
      _ = _ := by ring
  exact hsmall G hG b hb (hbρ.trans_le (min_le_right _ _)) hclose d hfit hphaseGlobal
    hmap hτ hs hτs hs1 hp hK' δ hδ.le hδτ u H hu hH hball hbu hmu

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
