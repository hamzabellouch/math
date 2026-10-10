import OAI.Geometry.Perimeter.Regularity.PhaseMomentLimit
import OAI.Geometry.Perimeter.Regularity.ActualFluxWindowLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem fiber_flux_first_moment {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {l u : ℝ} (hl : q l=1) (hu : q u=0) :
    (∫ s in l..u, s*(-deriv q s)) = l+∫ s in l..u, q s := by
  have h := intervalIntegral.integral_deriv_mul_eq_sub (a := l) (b := u)
    (fun s _ ↦ hasDerivAt_id s) (fun s _ ↦ (hq.differentiable (by simp) s).hasDerivAt)
    (continuous_const.intervalIntegrable _ _) (hq.continuous_deriv le_rfl |>.intervalIntegrable _ _)
  simp only [one_mul,hu,hl,mul_zero,mul_one,zero_sub,id_eq] at h
  have hi : IntervalIntegrable (fun s ↦ s*deriv q s) volume l u :=
    (continuous_id.mul (hq.continuous_deriv le_rfl)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hq.continuous.intervalIntegrable _ _) hi] at h
  simp_rw [mul_neg,intervalIntegral.integral_neg]
  linarith

theorem mollifiedNormalProfile_cap_values {E : Set (Euc n)}
    {v : Euc n} (hv : ‖v‖ = 1) {k : Euc n → ℝ} (hu : ∫ x, k x=1)
    {a b ε R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+ε < b)
    (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0))
    (y : normalPlane v) (hy : ‖y‖+b+ε ≤ R) :
    mollifiedNormalProfile E k v y (-b)=1 ∧ mollifiedNormalProfile E k v y b=0 := by
  constructor
  · apply phaseMollification_lower_cap hv hu ha hs hphase
    · have h := norm_add_le (y:Euc n) ((-b)•v)
      rw [norm_smul,hv,mul_one,Real.norm_eq_abs,abs_neg,abs_of_nonneg hb] at h
      change ‖(y:Euc n)‖+b+ε ≤ R at hy
      linarith
    · rw [normal_fiber_inner hv]; linarith
  · apply phaseMollification_upper_cap hv ha hs hphase
    · have h := norm_add_le (y:Euc n) (b•v)
      rw [norm_smul,hv,mul_one,Real.norm_eq_abs,abs_of_nonneg hb] at h
      change ‖(y:Euc n)‖+b+ε ≤ R at hy
      linarith
    · rw [normal_fiber_inner hv]; exact hab

theorem mollified_fiber_weighted_first_moment {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hu : ∫ x, k x = 1) {a b ε R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+ε < b)
    (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0))
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+ε ≤ R) :
    (∫ x, normalWindowTest v φ b 1 x * (-fderiv ℝ (phaseMollification E k) x v)) =
      ∫ y in tsupport φ, φ y*(-b+∫ s in (-b)..b, phaseMollification E k ((y:Euc n)+s•v)) := by
  have hd := ((phaseMollification_contDiff hE hk hc).continuous_fderiv (by simp)).clm_apply
    (g := fun _ ↦ v) continuous_const
  have hi := normalWindowTest_integral hv hφ hcφ hb 1 hd.neg
  dsimp only [Pi.neg_apply] at hi
  rw [hi]
  apply setIntegral_congr_fun hcφ.measurableSet
  intro y hy
  simp only [pow_one]
  simp_rw [← mollifiedNormalProfile_deriv hE hk hc v]
  have hcap := mollifiedNormalProfile_cap_values hv hu ha hb hab hs hphase y (hKR y hy)
  rw [fiber_flux_first_moment ((mollifiedNormalProfile_contDiff hE hk hc v y).of_le (by simp))
    hcap.1 hcap.2]
  rfl

theorem mollified_fiber_weighted_height_tendsto {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun j ↦ ∫ y in tsupport φ, φ y*
      (-b+∫ s in (-b)..b, phaseMollification E ((c1Mollifier j).normed volume)
        ((y:Euc n)+s•v))) atTop
      (𝓝 (∫ y in tsupport φ, φ y*exactFiberHeight E v b y)) := by
  apply tendsto_integral_of_dominated_convergence (fun y ↦ ‖φ y‖*b)
  · intro j
    exact (hφ.mul (continuous_const.add (continuous_profile_integral (v := v) _
      (phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous (-b) b))).aestronglyMeasurable
  · exact (hφ.continuousOn.integrableOn_compact hcφ).norm.mul_const _
  · intro j
    apply ae_of_all
    intro y
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h := interval_height_abs_le
      (((phaseMollification_contDiff hE (c1Mollifier j).contDiff_normed
        (c1Mollifier j).hasCompactSupport_normed).continuous.comp
          (continuous_const.add (continuous_id.smul continuous_const))).measurable)
      hb (fun s ↦ phaseMollification_c1_mem_Icc hE j ((y:Euc n)+s•v))
    exact h
  · filter_upwards [ae_restrict_of_ae (mollified_fiber_height_ae_tendsto hE hv hb)] with y hy
    exact tendsto_const_nhds.mul hy

theorem actual_fiber_signed_first_moment (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {a b δ R : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hab : a+δ < b) (hR : 0 < R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    (∫ x in Metric.ball 0 R, normalWindowTest v φ b 1 x *
      inner ℝ (approximateNormal E x) v ∂perimeterMeasure E) =
      ∫ y in tsupport φ, φ y*exactFiberHeight E v b y := by
  have hb : 0 ≤ b := by linarith
  have hh' : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| < b :=
    fun x hx ↦ (hh x hx).trans_lt (by linarith)
  have hA := actual_normal_flux_window_tendsto hn hmin hv hφ hcφ hb hδ hR 1 hKR hh'
  have hB := mollified_fiber_weighted_height_tendsto hmin.1 hv hφ hcφ hb
  apply tendsto_nhds_unique hA
  apply hB.congr'
  have he : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut < δ :=
    c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with j hj
  have hs : Function.support ((c1Mollifier (n := n) j).normed volume) ⊆ Metric.ball 0 δ := by
    intro x hx
    have hx' := subset_tsupport _ hx
    rw [(c1Mollifier j).tsupport_normed_eq] at hx'
    exact Metric.closedBall_subset_ball hj hx'
  exact (mollified_fiber_weighted_first_moment hmin.1 hv hφ hcφ
    (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed
    (c1Mollifier j).integral_normed ha hb hab hs hphase hKR).symm

end RPISingularHarnack

end

end OAI
