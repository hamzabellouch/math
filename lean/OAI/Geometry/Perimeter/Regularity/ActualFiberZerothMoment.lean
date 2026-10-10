import OAI.Geometry.Perimeter.Regularity.NormalFluxError
import OAI.Geometry.Perimeter.Regularity.ActualFiberFirstMoment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem mollified_fiber_weighted_zeroth_moment {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖=1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hu : ∫ x, k x=1) {a b ε R : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+ε<b)
    (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| → (x∈E ↔ inner ℝ v x<0))
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+ε≤R) :
    (∫ x, normalWindowTest v φ b 0 x*(-fderiv ℝ (phaseMollification E k) x v)) =
      ∫ y in tsupport φ, φ y := by
  have hd := ((phaseMollification_contDiff hE hk hc).continuous_fderiv (by simp)).clm_apply
    (g := fun _ ↦ v) continuous_const
  have hi := normalWindowTest_integral hv hφ hcφ hb 0 hd.neg
  dsimp only [Pi.neg_apply] at hi
  rw [hi]
  apply setIntegral_congr_fun hcφ.measurableSet
  intro y hy
  simp only [pow_zero,one_mul]
  simp_rw [← mollifiedNormalProfile_deriv hE hk hc v]
  have hq : ContDiff ℝ 1 (mollifiedNormalProfile E k v y) :=
    (mollifiedNormalProfile_contDiff hE hk hc v y).of_le (by simp)
  have hcap := mollifiedNormalProfile_cap_values hv hu ha hb hab hs hphase y (hKR y hy)
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ (hq.differentiable (by simp) s).hasDerivAt)
    ((hq.continuous_deriv le_rfl).intervalIntegrable _ _),hcap.1,hcap.2]
  ring

theorem actual_fiber_signed_zeroth_moment (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {a b δ R : ℝ} (ha : 0≤a) (hδ : 0<δ) (hab : a+δ<b) (hR : 0<R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ≤R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x|≤a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x∈E ↔ inner ℝ v x<0)) :
    (∫ x in Metric.ball 0 R, normalWindowTest v φ b 0 x*
      inner ℝ (approximateNormal E x) v ∂perimeterMeasure E) = ∫ y in tsupport φ, φ y := by
  have hb : 0≤b := by linarith
  have hh' : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x|<b :=
    fun x hx ↦ (hh x hx).trans_lt (by linarith)
  have hA := actual_normal_flux_window_tendsto hn hmin hv hφ hcφ hb hδ hR 0 hKR hh'
  apply tendsto_nhds_unique hA
  apply tendsto_const_nhds.congr'
  have he : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut<δ :=
    c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with j hj
  have hs : Function.support ((c1Mollifier (n := n) j).normed volume) ⊆ Metric.ball 0 δ := by
    intro x hx
    have hx' := subset_tsupport _ hx
    rw [(c1Mollifier j).tsupport_normed_eq] at hx'
    exact Metric.closedBall_subset_ball hj hx'
  exact (mollified_fiber_weighted_zeroth_moment hmin.1 hv hφ hcφ
    (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed
    (c1Mollifier j).integral_normed ha hb hab hs hphase hKR).symm

theorem actual_fiber_zeroth_moment_error (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {M a b δ R : ℝ} (hM : ∀ y, ‖φ y‖≤M)
    (ha : 0≤a) (hδ : 0<δ) (hab : a+δ<b) (hR : 0<R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ≤R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x|≤a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x∈E ↔ inner ℝ v x<0)) :
    |(∫ x in Metric.ball 0 R, normalWindowTest v φ b 0 x ∂perimeterMeasure E)-
      (∫ y in tsupport φ, φ y)| ≤ M/2*orientedTilt E v (Metric.ball 0 R) := by
  rw [← actual_fiber_signed_zeroth_moment hn hmin hv hφ hcφ ha hδ hab hR hKR hh hphase]
  have h := normal_flux_error_le_tilt hn hmin hv hR (normalWindowTest_measurable hφ b 0)
    (normalWindowTest_bound hM (by linarith : 0≤b) 0)
  simpa only [pow_zero,mul_one,div_mul_eq_mul_div] using h

end RPISingularHarnack

end

end OAI
