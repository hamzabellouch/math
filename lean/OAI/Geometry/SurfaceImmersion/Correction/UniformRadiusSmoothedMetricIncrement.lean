import OAI.Geometry.SurfaceImmersion.Geometry.MetricRadiusSmallIncrement
import OAI.Geometry.SurfaceImmersion.Correction.UniformSmoothingInputProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds
import OAI.Geometry.SurfaceImmersion.Correction.GlobalSmoothedMetricStep
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry
import OAI.Geometry.SurfaceImmersion.Correction.SmoothedInputAdmissibility

namespace OAI

/-! One fixed geometric neighborhood supports smoothed metric correction at
every smoothing and cancellation order. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance uniformRadiusSmoothedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformRadiusSmoothedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformRadiusSmoothedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformRadiusSmoothedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformRadiusSmoothedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformRadiusSmoothedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- The two geometric radii are fixed before all smoothing orders,
correction orders, and true-input bounds. -/
theorem uniform_radius_smoothed_increment (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ a ρ : ℝ, 0 < a ∧ 0 < ρ ∧
    ∀ (r q : ℕ) (B₀ : ℝ), 0 ≤ B₀ →
    ∃ (η : ℝ) (B T : ℕ → ℝ), 0 < η ∧ η ≤ 1 ∧
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
    ∀ (G : M → Space) (H : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      (∀ p v w, H p v w = H p w v) →
    ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
      d.A.InputBound t r B₀ G H →
    ∀ b : ℝ, 0 ≤ b → b < ρ → d.A.WeightedBound 1 2 b (d.A.smooth r s G-F) →
    ∀ δ δ' τ : ℝ, 0 < δ → 0 ≤ δ' → δ' ≤ δ →
      0 < τ → τ ≤ s → τ/s ≤ η → δ ≤ τ →
      (∀ x, ‖d.A.tensorEncode (d.A.tensorSmooth r s H - (δ'/δ)^2 • g.inner) x -
        d.A.tensorEncode g.inner x‖ ≤ a/2) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, d.A.WeightedBound τ m (B m*(δ*τ)) U) ∧
        (∀ m, d.A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (realizedTensorError g.inner (d.A.tensorSmooth r s H) δ δ' (d.A.smooth r s G) U)) := by
  classical
  obtain ⟨a,ρ,ha,hρ,hsmall⟩ := d.uniform_radius_small_increment hF
  refine ⟨a,ρ,ha,hρ,?_⟩
  intro r q B₀ hB₀
  obtain ⟨PG,CH,hPG,hCH,hprofiles⟩ := d.A.uniform_smoothing_input_profiles r B₀ hB₀
  choose CG hCG hgBound using fun m => d.A.exists_bundle_bound
    d.A.tensorTriv d.A.tensorTriv_domain m g.contMDiff
  let C := fun m => CH m + CG m
  have hC (m : ℕ) : 1 ≤ C m := (hCH m).trans (le_add_of_nonneg_right (hCG m))
  obtain ⟨η,B,T,hη,hη1,hB,hT,hbuild⟩ := hsmall PG hPG q C hC
  refine ⟨η,B,T,hη,hη1,hB,hT,?_⟩
  intro G H hG hH hsym t s ht ht1 hs hs1 hinput b hb hbρ hnear δ δ' τ
    hδ hδ' hδ'δ hτ hτs hτη hδτ hTensorNear
  obtain ⟨hPG',hCH'⟩ := hprofiles G H t s ht ht1 hs hs1 hG hH hinput
  let α := (δ'/δ)^2
  have hα : 0 ≤ α := sq_nonneg _
  have hα1 : α ≤ 1 := by
    have hdiv : 0 ≤ δ'/δ := div_nonneg hδ' hδ.le
    have hdiv1 : δ'/δ ≤ 1 := (div_le_one hδ).mpr hδ'δ
    dsimp [α]
    nlinarith
  have hHs := d.A.tensorSmooth_smooth r hs hH
  have htarget : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p ((d.A.tensorSmooth r s H - α • g.inner) p)) :=
    hHs.sub_section g.contMDiff.const_smul_section
  have htargetBound (m : ℕ) : d.A.TensorWeightedBound s m (C m)
      (d.A.tensorSmooth r s H - α • g.inner) := by
    have hgb : d.A.TensorWeightedBound s m (CG m) g.inner :=
      fun i => (hgBound m i).shrink_scale hs.le hs1
    have hαg := d.A.tensorWeightedBound_const_smul g.contMDiff hgb α
    have hαg' : d.A.TensorWeightedBound s m (CG m) (α • g.inner) := by
      intro i
      apply (hαg i).mono_const
      rw [abs_of_nonneg hα]
      exact mul_le_of_le_one_left (hCG m) hα1
    exact d.A.tensorWeightedBound_sub hHs g.contMDiff.const_smul_section hs.le (hCH' m) hαg'
  have htargetSym : ∀ p v w,
      (d.A.tensorSmooth r s H - α • g.inner) p v w =
      (d.A.tensorSmooth r s H - α • g.inner) p w v := by
    intro p v w
    simp only [Pi.sub_apply,Pi.smul_apply,sub_apply,
      smul_apply,smul_eq_mul]
    rw [d.A.tensorSmooth_symmetric r hs hH hsym p v w,g.symm p v w]
  obtain ⟨U,hU,hUB,hUT⟩ := hbuild (d.A.smooth r s G) (d.A.smooth_smooth r hs hG)
    b hb hbρ hnear ⟨s,hs.le⟩ hs hs1 hPG'
    (d.A.tensorSmooth r s H - α • g.inner) htarget htargetSym hTensorNear htargetBound
    τ δ hτ hτs hτη hδ hδτ
  refine ⟨U,hU,hUB,?_⟩
  have hαδ : δ^2*α = δ'^2 := by dsimp [α]; field_simp [hδ.ne']
  have he : δ^2 • (d.A.tensorSmooth r s H - α • g.inner) =
      δ^2 • d.A.tensorSmooth r s H - δ'^2 • g.inner := by
    rw [smul_sub,smul_smul,hαδ]
  intro m
  convert hUT m using 1 <;> first | rfl | simp only [realizedTensorError,he]

/-- The metric norm bound is fixed once, and the smoothing-tail constant
is chosen from the smoothing order before the correction order or input bound. -/
theorem uniform_radius_smoothed_increment_of_input (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ a ρ K : ℝ, 0 < a ∧ 0 < ρ ∧ 0 ≤ K ∧
    ∀ r : ℕ, ∃ D : ℝ, 0 ≤ D ∧
    ∀ (q : ℕ) (B₀ : ℝ), 0 ≤ B₀ →
    ∃ (η : ℝ) (B T : ℕ → ℝ), 0 < η ∧ η ≤ 1 ∧
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
    ∀ (G : M → Space) (H : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      (∀ p v w, H p v w = H p w v) →
    ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s → s ≤ t →
      d.A.InputBound t r B₀ G H →
      d.A.WeightedBound 1 2 (ρ/4) (G-F) →
      (∀ x, ‖d.A.tensorEncode H x - d.A.tensorEncode g.inner x‖ ≤ a/8) →
      D*B₀*(s/t)^r ≤ min (ρ/4) (a/8) →
    ∀ δ δ' τ : ℝ, 0 < δ → 0 ≤ δ' → δ' ≤ δ →
      0 < τ → τ ≤ s → τ/s ≤ η → δ ≤ τ → (δ'/δ)^2*K ≤ a/8 →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, d.A.WeightedBound τ m (B m*(δ*τ)) U) ∧
        (∀ m, d.A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (realizedTensorError g.inner (d.A.tensorSmooth r s H) δ δ' (d.A.smooth r s G) U)) := by
  obtain ⟨a,ρ,ha,hρ,hsmoothed⟩ := d.uniform_radius_smoothed_increment hF
  obtain ⟨K,hK,hKb⟩ := d.A.exists_bundle_bound d.A.tensorTriv d.A.tensorTriv_domain 0 g.contMDiff
  have hgBound (x : JetPolynomial.Base) : ‖d.A.tensorEncode g.inner x‖ ≤ K :=
    (d.A.tensorEncode_bound g.contMDiff zero_lt_one hK hKb).norm_le (mem_univ x)
  refine ⟨a,ρ,K,ha,hρ,hK,?_⟩
  intro r
  obtain ⟨D,hD,hadmissible⟩ := d.A.smoothed_input_admissibility r
  refine ⟨D,hD,?_⟩
  intro q B₀ hB₀
  obtain ⟨η,B,T,hη,hη1,hB,hT,hstep⟩ := hsmoothed r q B₀ hB₀
  refine ⟨η,B,T,hη,hη1,hB,hT,?_⟩
  intro G H hG hH hsym t s ht ht1 hs hst hinput hnear hHnear htail δ δ' τ
    hδ hδ' hδ'δ hτ hτs hτη hδτ hratio
  have had := hadmissible g F G H ρ a (ρ/4) B₀ t s ((δ'/δ)^2) K
    hρ ha hB₀ hs hst ht1 hF hG hH hinput hnear le_rfl hHnear htail
    (sq_nonneg _) hgBound hratio
  exact hstep G H hG hH hsym t s ht ht1 hs (hst.trans ht1) hinput
    (ρ/2) (by positivity) (by linarith) had.1
    δ δ' τ hδ hδ' hδ'δ hτ hτs hτη hδτ had.2

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
