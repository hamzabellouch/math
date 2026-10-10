import OAI.Geometry.Perimeter.Regularity.GraphFluxWeight

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem full_graph_weak_minimal_equation (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0≤a) (ha4 : a<1/4)
    (hs : FullSlab E v 8 a) {f : normalPlane v → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    {ψ : normalPlane v → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ Metric.ball 0 (1/4)) :
    (∫ y, inner ℝ (gradient f y) (gradient ψ y)/Real.sqrt (1+‖gradient f y‖^2))=0 := by
  let φ := graphFluxWeight v f ψ
  have hφ : Continuous φ := graphFluxWeight_continuous hv hf hψ hsψ
  have hcφ : HasCompactSupport φ := hcψ.of_isClosed_subset (isClosed_tsupport _)
    (graphFluxWeight_tsupport f ψ)
  have hsφ : tsupport φ ⊆ Metric.ball 0 (1/4) := (graphFluxWeight_tsupport f ψ).trans hsψ
  let χ : ContDiffBump (0:ℝ) := ⟨1/3,1/2,by norm_num,by norm_num⟩
  have hχone : ∀ t : ℝ, |t|<1/3 → χ t=1 := by
    intro t ht
    exact χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] using ht.le)
  let Ψ := normalTestLift v ψ χ
  have hcΨ : tsupport Ψ ⊆ Metric.closedBall 0 (1/4+1/2) :=
    normalTestLift_tsupport hv ψ χ (subset_closure.trans (hsψ.trans Metric.ball_subset_closedBall))
      (by simpa only [χ.support_eq] using (Metric.ball_subset_closedBall : Metric.ball (0:ℝ) (1/2) ⊆ Metric.closedBall 0 (1/2)))
  have hΨ := normalTestLift_contDiff hψ χ.contDiff
  have hzero := minimizing_tangentialGradient_integral_eq_zero_local hn hmin 0 (by norm_num : (0:ℝ)<1)
    hΨ ((isCompact_closedBall 0 (1/4+1/2)).of_isClosed_subset (isClosed_tsupport _) hcΨ)
    (hcΨ.trans (Metric.closedBall_subset_ball (by norm_num))) v
  have hslab := hs.mono_radius (by norm_num : (1:ℝ)≤8)
  have hdegree := actual_fiber_signed_zeroth_moment hn hmin hv hφ hcφ ha
    (by norm_num : (0:ℝ)<1/8) (by linarith : a+1/8<1/2) (by norm_num : (0:ℝ)<1)
    (fun y hy ↦ by
      have hy' : ‖y‖<1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hsφ hy
      linarith : ∀ y∈tsupport φ, ‖y‖+1/2+1/8≤1) hslab.1 hslab.2
  have heq : (∫ x in Metric.ball 0 1, inner ℝ (tangentialGradient E Ψ x) v ∂perimeterMeasure E)=
      ∫ x in Metric.ball 0 1, normalWindowTest v φ (1/2) 0 x*
        inner ℝ (approximateNormal E x) v ∂perimeterMeasure E := by
    apply integral_congr_ae
    have hsupport : ∀ᵐ x ∂perimeterMeasure E, x∈perimeterSupport E := by
      rw [←perimeterMeasure_support]; exact (perimeterMeasure E).support_mem_ae
    filter_upwards [ae_restrict_of_ae hsupport,ae_restrict_mem measurableSet_ball] with x hxS hxB
    have hxheight := hslab.1 x ⟨hxS,hxB⟩
    have hwindow : normalWindowTest v φ (1/2) 0 x=φ (normalProjection v x) := by
      simp only [normalWindowTest,Set.indicator_of_mem (show x∈{z | |inner ℝ v z|≤1/2} from by
        change |inner ℝ v x|≤1/2; linarith),pow_zero,mul_one]
    rw [hwindow]
    by_cases hxP : normalProjection v x∈tsupport ψ
    · have hxC : x∈graphCylinder v := ⟨by
        simpa only [Metric.mem_ball,dist_zero_right] using hsψ hxP,by linarith⟩
      exact graphTest_tangential_flux hv (hψ.differentiable (by simp)) hχone (by linarith)
        (graph_approximateNormal hn hmin hv ha ha4 hs hf hiff hxC hxS)
    · change inner ℝ (gradient Ψ x - (inner ℝ (gradient Ψ x) (approximateNormal E x)) • approximateNormal E x) v = _
      rw [show gradient Ψ x=0 from normalTestLift_gradient_zero hxP]
      simp [φ,graphFluxWeight_zero hxP]
  rw [heq,hdegree,setIntegral_tsupport] at hzero
  simpa only [φ,graphFluxWeight,graphAreaFactor_sqrt hv] using hzero

end RPISingularHarnack

end

end OAI
