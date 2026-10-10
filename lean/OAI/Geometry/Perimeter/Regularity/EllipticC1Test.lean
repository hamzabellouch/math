import OAI.Geometry.Perimeter.Regularity.EllipticLinearStep

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem gradient_tsupport_subset (f : Euc n → ℝ) : tsupport (gradient f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra h
  have hd := fderiv_of_notMem_tsupport ℝ h
  have hg : gradient f x=0 := by simp only [gradient,hd,map_zero]
  exact hx hg

 theorem gradient_norm_eq_fderiv (f : Euc n → ℝ) (x : Euc n) : ‖gradient f x‖=‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ (Euc n)).symm.norm_map _

 theorem integral_inner_gradient_eq_setIntegral {G : Euc n → Euc n} {φ : Euc n → ℝ}
    {U : Set (Euc n)} (hU : MeasurableSet U) (hs : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (G x) (gradient φ x)) = ∫ x in U, inner ℝ (G x) (gradient φ x) := by
  rw [←integral_indicator hU]
  congr 1; funext x
  by_cases hx : x∈U
  · simp [hx]
  · have hg : gradient φ x=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs (gradient_tsupport_subset φ h)))
    simp [hx,hg]

 theorem mollified_gradient_pairing_tendsto {G : Euc n → Euc n} (hG : Continuous G)
    (p : Euc n) (r : ℝ)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    : Tendsto (fun j ↦ ∫ x in Metric.ball p r, inner ℝ (G x) (gradient (RPI.Boundary.c1Mollify φ j) x)) atTop
      (𝓝 (∫ x in Metric.ball p r, inner ℝ (G x) (gradient φ x))) := by
  let φj := RPI.Boundary.c1Mollify φ
  obtain ⟨M,hM,hb⟩ := RPI.Boundary.c1Mollify_uniform_bound hφ hcφ
  obtain ⟨C,hC⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn hG.continuousOn
  have : IsFiniteMeasure (volume.restrict (Metric.ball p r)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ |C| * M)
  · intro j
    exact (hG.inner (gradient_continuous_C1 ((RPI.Boundary.c1Mollify_contDiff hφ.continuous j).of_le (by simp)))).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    calc
      ‖inner ℝ (G x) (gradient (φj j) x)‖ ≤ ‖G x‖*‖gradient (φj j) x‖ := norm_inner_le_norm _ _
      _ ≤ |C| * M := mul_le_mul ((hC x (Metric.ball_subset_closedBall hx)).trans (le_abs_self C))
        (by rw [gradient_norm_eq_fderiv]; exact (hb j x).2) (norm_nonneg _) (abs_nonneg _)
  · apply ae_of_all
    intro x
    have hg : Tendsto (fun j ↦ gradient (φj j) x) atTop (𝓝 (gradient φ x)) := by
      exact (InnerProductSpace.toDual ℝ (Euc n)).symm.continuous.tendsto (fderiv ℝ φ x) |>.comp
        (RPI.Boundary.c1Mollify_fderiv_tendsto hφ hcφ x)
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ G x) atTop (𝓝 (G x))).inner hg

 theorem continuous_div_free_C1_test {G : Euc n → Euc n} (hG : Continuous G)
    (p : Euc n) (r : ℝ)
    (h : ∀ φ : SmoothLocalTest (Metric.ball p r), (∫ x, inner ℝ (G x) (gradient φ.val x))=0)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball p r) :
    (∫ x, inner ℝ (G x) (gradient φ x))=0 := by
  let φj := RPI.Boundary.c1Mollify φ
  have hs := RPI.Boundary.c1Mollify_eventually_tsupport_subset hcφ Metric.isOpen_ball hsφ
  have hlim := mollified_gradient_pairing_tendsto hG p r hφ hcφ
  have hz : ∀ᶠ j in atTop, (∫ x in Metric.ball p r, inner ℝ (G x) (gradient (φj j) x))=0 := by
    filter_upwards [hs] with j hj
    rw [←integral_inner_gradient_eq_setIntegral measurableSet_ball hj]
    exact h ⟨φj j,RPI.Boundary.c1Mollify_contDiff hφ.continuous j,
      RPI.Boundary.c1Mollify_hasCompactSupport hcφ j,hj⟩
  rw [integral_inner_gradient_eq_setIntegral measurableSet_ball hsφ]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hz.mono (fun _ hj ↦ hj.symm)))

 theorem WeakLinearEquation.test_C1 {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} (hA : Continuous A) (hf : ContDiff ℝ 1 f)
    (hF : Continuous F) {p : Euc n} {r : ℝ} (h : WeakLinearEquation A f F (Metric.ball p r))
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball p r) :
    (∫ x, inner ℝ (A x (gradient f x)-F x) (gradient φ x))=0 := by
  apply continuous_div_free_C1_test ((hA.clm_apply (gradient_continuous_C1 hf)).sub hF) p r _ hφ hcφ hsφ
  intro ψ
  change (∫ x, inner ℝ (A x (gradient f x)-F x) (gradient ψ.val x))=0
  simp_rw [inner_sub_left]
  erw [integral_sub (inner_gradient_pairing_integrable (hA.clm_apply (gradient_continuous_C1 hf)) ψ)
    (inner_gradient_pairing_integrable hF ψ),h ψ,sub_self]

end RPISingularHarnack

end

end OAI
