import OAI.Geometry.SurfaceImmersion.Geometry.MetricSmallIncrement
import OAI.Geometry.SurfaceImmersion.Correction.UniformSmoothingInputProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds
import OAI.Geometry.SurfaceImmersion.Correction.GlobalSmoothedMetricStep
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry
import OAI.Geometry.SurfaceImmersion.Correction.SmoothedInputAdmissibility

namespace OAI

/-! An actual metric-adapted immersion supplies all the small-increment geometry. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance smoothedMetricIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance smoothedMetricIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance smoothedMetricIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance smoothedMetricIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance smoothedMetricIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance smoothedMetricIncrementSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- A finite true-input bound supplies every analytic profile used to
construct the increment at the smoothed map. All constants and thresholds
precede the true input, its higher derivatives, and the three scales. -/
theorem smoothed_increment (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (r q : ℕ) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ a ρ η : ℝ, 0 < a ∧ 0 < ρ ∧ 0 < η ∧ η ≤ 1 ∧
    ∃ B T : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
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
  obtain ⟨PG,CH,hPG,hCH,hprofiles⟩ := d.A.uniform_smoothing_input_profiles r B₀ hB₀
  choose PF hPF hbase using fun m => d.A.exists_shifted_bound 2 m hF
  choose CG hCG hgBound using fun m => d.A.exists_bundle_bound
    d.A.tensorTriv d.A.tensorTriv_domain m g.contMDiff
  let P := fun m => PG m + PF m
  have hP (m : ℕ) : 0 ≤ P m := add_nonneg (hPG m) (hPF m)
  have hPF' (m : ℕ) : d.A.ShiftedBound 2 m 1 (P m) F := by
    intro i j hj x
    exact (hbase m i j hj x).trans (le_add_of_nonneg_left (hPG m))
  let C := fun m => CH m + CG m
  have hC (m : ℕ) : 1 ≤ C m := (hCH m).trans (le_add_of_nonneg_right (hCG m))
  obtain ⟨a,ha,hstep⟩ := d.small_increment hF P hP hPF' q
  obtain ⟨ρ,η,B,T,hρ,hη,hη1,hB,hT,hbuild⟩ := hstep C hC
  refine ⟨a,ρ,η,ha,hρ,hη,hη1,B,T,hB,hT,?_⟩
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
  have hmapBound (m : ℕ) : d.A.ShiftedBound 2 m s (P m) (d.A.smooth r s G) := by
    intro i j hj x
    exact (hPG' m i j hj x).trans (le_add_of_nonneg_right (hPF m))
  have htargetSym : ∀ p v w,
      (d.A.tensorSmooth r s H - α • g.inner) p v w =
      (d.A.tensorSmooth r s H - α • g.inner) p w v := by
    intro p v w
    simp only [Pi.sub_apply,Pi.smul_apply,sub_apply,
      smul_apply,smul_eq_mul]
    rw [d.A.tensorSmooth_symmetric r hs hH hsym p v w,g.symm p v w]
  obtain ⟨U,hU,hUB,hUT⟩ := hbuild (d.A.smooth r s G) (d.A.smooth_smooth r hs hG)
    b hb hbρ hnear ⟨s,hs.le⟩ hs hs1 hmapBound
    (d.A.tensorSmooth r s H - α • g.inner) htarget htargetSym hTensorNear htargetBound
    τ δ hτ hτs hτη hδ hδτ
  refine ⟨U,hU,hUB,?_⟩
  have hαδ : δ^2*α = δ'^2 := by dsimp [α]; field_simp [hδ.ne']
  have he : δ^2 • (d.A.tensorSmooth r s H - α • g.inner) =
      δ^2 • d.A.tensorSmooth r s H - δ'^2 • g.inner := by
    rw [smul_sub,smul_smul,hαδ]
  intro m
  convert hUT m using 1 <;> first | rfl | simp only [realizedTensorError,he]

/-- The low-norm bootstrap gives the required neighborhoods of the
smoothed input, so no smoothed-map hypothesis is needed by the iteration. -/
theorem smoothed_increment_of_input (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (r q : ℕ) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ a ρ η D K : ℝ, 0 < a ∧ 0 < ρ ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ D ∧ 0 ≤ K ∧
    ∃ B T : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
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
  obtain ⟨a,ρ,η,ha,hρ,hη,hη1,B,T,hB,hT,hstep⟩ := d.smoothed_increment hF r q hB₀
  obtain ⟨D,hD,hadmissible⟩ := d.A.smoothed_input_admissibility r
  obtain ⟨K,hK,hKb⟩ := d.A.exists_bundle_bound d.A.tensorTriv d.A.tensorTriv_domain 0 g.contMDiff
  have hgBound (x : JetPolynomial.Base) : ‖d.A.tensorEncode g.inner x‖ ≤ K :=
    (d.A.tensorEncode_bound g.contMDiff zero_lt_one hK hKb).norm_le (mem_univ x)
  refine ⟨a,ρ,η,D,K,ha,hρ,hη,hη1,hD,hK,B,T,hB,hT,?_⟩
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
