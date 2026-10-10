import OAI.Geometry.Perimeter.Regularity.WeightedFiberMoment
import OAI.Geometry.Perimeter.Regularity.WeightedWrongWayFlux

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem actual_fiber_signed_second_moment (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : ∀ y, 0 ≤ φ y)
    {M a b δ R : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hab : a+δ < b) (hR : 0 < R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    let A := ∫ x in Metric.ball 0 R, normalWindowTest v φ b 2 x *
      inner ℝ (approximateNormal E x) v ∂perimeterMeasure E
    let B := ∫ y in tsupport φ, φ y*(exactFiberHeight E v b y)^2
    0 ≤ A-B ∧ A-B ≤ 4*b^2*M*orientedTilt E v (Metric.ball 0 R) := by
  dsimp only
  have hb : 0 ≤ b := by linarith
  have hh' : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| < b :=
    fun x hx ↦ (hh x hx).trans_lt (by linarith)
  have hA := actual_normal_flux_window_tendsto hn hmin hv hφ hcφ hb hδ hR 2 hKR hh'
  have hB := mollified_fiber_weighted_height_square_tendsto hmin.1 hv hφ hcφ hb
  have hD := normalWindowTest_diffuse_tendsto_zero hmin.1 hv hφ hcφ b
  have he : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut < δ :=
    c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hδ)
  have hdef : ∀ᶠ j in atTop,
      let q := phaseMollification E ((c1Mollifier j).normed volume)
      let A := ∫ x, normalWindowTest v φ b 2 x * (-fderiv ℝ q x v)
      let B := ∫ y in tsupport φ, φ y*(-b+∫ s in (-b)..b, q ((y:Euc n)+s•v))^2
      0 ≤ A-B ∧ A-B ≤
        4*b*(∫ x, normalWindowTest v φ b 0 x * (q x*(1-q x))) +
        4*b^2*M*orientedTilt E v (Metric.ball 0 R) := by
    filter_upwards [he] with j hj
    have hs : Function.support ((c1Mollifier (n := n) j).normed volume) ⊆ Metric.ball 0 δ := by
      intro x hx
      have hx' := subset_tsupport _ hx
      rw [(c1Mollifier j).tsupport_normed_eq] at hx'
      exact Metric.closedBall_subset_ball hj hx'
    have ht := mollified_fiber_weighted_defect hmin.1 hv hφ hcφ hpφ
      (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed
      (c1Mollifier j).nonneg_normed (c1Mollifier j).integral_normed ha hb hab hs hphase hKR
    have hp := weighted_positive_derivative_le_tilt hn hmin hv hφ hcφ hpφ hM hb hR hKR hj
    dsimp only at ht ⊢
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8*b^2)
    nlinarith
  refine ⟨ge_of_tendsto (hA.sub hB) (hdef.mono fun j hj ↦ hj.1),?_⟩
  have ht := le_of_tendsto_of_tendsto (hA.sub hB)
    ((hD.const_mul (4*b)).add_const (4*b^2*M*orientedTilt E v (Metric.ball 0 R)))
    (hdef.mono fun j hj ↦ hj.2)
  simpa only [mul_zero,zero_add] using ht

end RPISingularHarnack

end

end OAI
