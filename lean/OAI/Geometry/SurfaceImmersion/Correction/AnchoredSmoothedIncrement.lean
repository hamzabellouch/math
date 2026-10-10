import OAI.Geometry.SurfaceImmersion.Atlas.AnchoredAtlasIncrement
import OAI.Geometry.SurfaceImmersion.Geometry.ReadJetBallBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSmoothingProfiles
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialReadProfiles
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry
import OAI.Geometry.SurfaceImmersion.Correction.GlobalSmoothedMetricStep

namespace OAI

/-! The actual anchored increment at the smoothed input, with polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
local instance anchoredSmoothFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredSmoothFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredSmoothDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredSmoothDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredSmoothSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredSmoothSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_smoothed_increment (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ (r q : ℕ) (Budget : ℝ → ℝ), HasPolynomialBound Budget →
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (Q m)) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y),
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      (∀ y v w, H y v w = H y w v) →
    ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
      A.InputBound t r (Budget z⁻¹) G H →
      A.WeightedBound 1 2 (z^4/D) (A.smooth r s G-F) →
    ∀ δ δ' τ : ℝ, 0 < δ → 0 ≤ δ' → δ' ≤ δ → 0 < τ → τ ≤ s → δ ≤ τ →
      τ/s ≤ min 1 ((a-a/2)/(2*(E*(z⁻¹)^e))) →
      (∀ y, ‖A.tensorEncode (A.tensorSmooth r s H-(δ'/δ)^2 • g.inner) y-
        A.tensorEncode g.inner y‖ ≤ a/2) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
          (realizedTensorError g.inner (A.tensorSmooth r s H) δ δ' (A.smooth r s G) U)) := by
  classical
  obtain ⟨z₀,a,hz₀,hz₀1,ha,hstep⟩ := A.anchored_atlas_increment g houter R c B b hc hB hb
  obtain ⟨D,hD,hball⟩ := A.readJetBall_radius
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro r q Budget hBudget
  obtain ⟨PG,CH,hPG,hCH,hCH1,hprofiles⟩ := A.polynomial_smoothing_input_profiles r Budget hBudget
  obtain ⟨FJ,hFJ,hFJ1,hreads⟩ := A.polynomial_plane_read_profiles PG hPG
  choose CG hCG hgb using fun m => A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain m g.contMDiff
  let Y := fun m x => CH m x+CG m
  have hY (m : ℕ) : HasPolynomialBound (Y m) := (hCH m).add (polynomialBound_const (hCG m))
  have hY1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Y m x :=
    (hCH1 m x hx).trans (le_add_of_nonneg_right (hCG m))
  obtain ⟨e,E,P,Q,hE,hP,hQ,hbuild⟩ := hstep FJ Y hFJ hY hFJ1 hY1 q
  refine ⟨e,E,P,Q,hE,hP,hQ,?_⟩
  intro z hz hzsmall F hF hFb hFm G H hG hH hsym t s ht ht1 hs hs1
    hinput hnear δ δ' τ hδ hδ' hδ'δ hτ hτs hδτ hsmall hTensorNear
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  obtain ⟨hPG',hCH'⟩ := hprofiles z⁻¹ hx G H t s ht ht1 hs hs1 hG hH hinput
  let α := (δ'/δ)^2
  have hα : 0 ≤ α := sq_nonneg _
  have hα1 : α ≤ 1 := by
    have hdiv : 0 ≤ δ'/δ := div_nonneg hδ' hδ.le
    have hdiv1 : δ'/δ ≤ 1 := (div_le_one hδ).mpr hδ'δ
    dsimp [α]; nlinarith
  have hGs := A.smooth_smooth r hs hG
  have hHs := A.tensorSmooth_smooth r hs hH
  have htarget : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun y => TotalSpace.mk' TensorFiber y ((A.tensorSmooth r s H-α • g.inner) y)) :=
    hHs.sub_section g.contMDiff.const_smul_section
  have htargetBound (m : ℕ) : A.TensorWeightedBound s m (Y m z⁻¹)
      (A.tensorSmooth r s H-α • g.inner) := by
    have hmetric : A.TensorWeightedBound s m (CG m) g.inner :=
      fun i => (hgb m i).shrink_scale hs.le hs1
    have hscaled := A.tensorWeightedBound_const_smul g.contMDiff hmetric α
    have hscaled' : A.TensorWeightedBound s m (CG m) (α • g.inner) := by
      intro i
      apply (hscaled i).mono_const
      rw [abs_of_nonneg hα]
      exact mul_le_of_le_one_left (hCG m) hα1
    exact A.tensorWeightedBound_sub hHs g.contMDiff.const_smul_section hs.le (hCH' m) hscaled'
  have htargetSym : ∀ y v w,
      (A.tensorSmooth r s H-α • g.inner) y v w = (A.tensorSmooth r s H-α • g.inner) y w v := by
    intro y v w
    simp only [Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,smul_eq_mul]
    rw [A.tensorSmooth_symmetric r hs hH hsym y v w,g.symm y v w]
  obtain ⟨U,hU,hsize,herror⟩ := hbuild z hz hzsmall F hF hFb hFm
    (A.smooth r s G) (hball z F (A.smooth r s G) hF hGs hnear)
    τ ⟨s,hs.le⟩ hτ hs hτs hs1 (hreads z⁻¹ hx (A.smooth r s G) hGs s hs hs1 hPG')
    hsmall (A.tensorSmooth r s H-α • g.inner) htarget htargetSym hTensorNear htargetBound δ hδ hδτ
  refine ⟨U,hU,hsize,?_⟩
  have hαδ : δ^2*α = δ'^2 := by dsimp [α]; field_simp [hδ.ne']
  have he : δ^2 • (A.tensorSmooth r s H-α • g.inner) =
      δ^2 • A.tensorSmooth r s H-δ'^2 • g.inner := by
    rw [smul_sub,smul_smul,hαδ]
  intro m
  convert herror m using 1 <;> first | rfl | simp only [realizedTensorError,he]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
