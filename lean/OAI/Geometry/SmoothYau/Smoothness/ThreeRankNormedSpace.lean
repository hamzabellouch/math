import Mathlib
import OAI.Geometry.SmoothYau.ProductMetric.ThreeMeridianNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeRankNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeRankContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
section Curve
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma inChart_deriv_curve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (c : ℝ) :
    fderiv ℝ (u ∘ (chartAt E (γ c)).symm) ((chartAt E (γ c)) (γ c))
      (deriv ((chartAt E (γ c)) ∘ γ) c)=deriv (u ∘ γ) c := by
  let e := chartAt E (γ c)
  have he : γ c ∈ e.source := mem_chart_source E (γ c)
  have hc : ContDiffAt ℝ ∞ (e ∘ γ) c :=
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (γ c)) he).comp c hγ.contMDiffAt).contDiffAt
  have hf := (contDiffAt_inChart hu (γ c) (e.map_source he)).differentiableAt (by simp)
  have hder := hf.hasFDerivAt.comp_hasDerivAt c (hc.differentiableAt (by simp)).hasDerivAt
  have hEq : (u ∘ e.symm) ∘ (e ∘ γ) =ᶠ[𝓝 c] u ∘ γ := by
    filter_upwards [hγ.continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds he)] with t ht
    simp only [Function.comp_apply,e.left_inv ht]
  simpa only [e] using (hder.congr_of_eventuallyEq hEq.symm).deriv.symm
lemma linear_prod_surjective_of_directions (L R : E →L[ℝ] ℝ) (v w : E)
    (hLv : L v ≠ 0) (hLw : L w=0) (hRw : R w≠0) : Function.Surjective (L.prod R) := by
  rintro ⟨a,b⟩
  refine ⟨(a/L v) • v+((b-(a/L v)*R v)/R w) • w,?_⟩
  apply Prod.ext
  · change L ((a/L v) • v+((b-(a/L v)*R v)/R w) • w)=a
    simp only [map_add,map_smul,smul_eq_mul,hLw,mul_zero,add_zero]
    exact div_mul_cancel₀ a hLv
  · change R ((a/L v) • v+((b-(a/L v)*R v)/R w) • w)=b
    simp only [map_add,map_smul,smul_eq_mul]
    rw [div_mul_cancel₀ _ hRw]
    ring
end Curve

def threeMeridianEnergy (r : ℝ) (m : ℕ) : ℝ → ℝ :=
  coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
    (threeCoupled r (4*m+1)) ∘ threeMeridian
lemma threeMeridianEnergy_smooth (r : ℝ) (m : ℕ) : ContDiff ℝ ∞ (threeMeridianEnergy r m) :=
  ((contMDiff_coordinateGradientPair (threeCoupled_smooth r _) (threeCoupled_smooth r _)
    threeBackgroundMetric).comp threeMeridian_smooth).contDiff
lemma threeMeridianEnergy_zero (r : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    threeMeridianEnergy r m 0=2*(4*(m:ℝ)+1)^2 := by
  rw [threeMeridianEnergy,Function.comp_apply,threeMeridian_gradient_value]
  simp [show 4*m≠0 by omega]
  ring
lemma threeMeridianEnergy_right (r : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    threeMeridianEnergy r m (Real.pi/2)=2*(4*(m:ℝ)+1)^2*(r^(4*m+1))^2 := by
  rw [threeMeridianEnergy,Function.comp_apply,threeMeridian_gradient_value]
  simp [show 4*m≠0 by omega]
  ring
lemma exists_threeMeridianEnergy_deriv (r : ℝ) (hr : 0<r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c ∈ Ioo 0 (Real.pi/2), deriv (threeMeridianEnergy r m) c ≠ 0 := by
  have hd := (threeMeridianEnergy_smooth r m).differentiable (by simp)
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope (threeMeridianEnergy r m) (by positivity : (0:ℝ)<Real.pi/2)
    (threeMeridianEnergy_smooth r m).continuous.continuousOn hd.differentiableOn
  refine ⟨c,hc,?_⟩
  rw [he,div_ne_zero_iff,sub_ne_zero]
  constructor
  · rw [threeMeridianEnergy_right r hm,threeMeridianEnergy_zero r hm]
    have hp : (r^(4*m+1))^2<1 := by
      rw [←pow_mul]
      exact pow_lt_one₀ hr.le hr1 (by omega)
    have hk : 0<2*(4*(m:ℝ)+1)^2 := by positivity
    nlinarith
  · linarith [Real.pi_pos]
lemma threeMeridian_circle_deriv_ne (r : ℝ) (hr : 0<r) (m : ℕ) {c : ℝ}
    (hc : c ∈ Ioo 0 (Real.pi/2)) :
    fderiv ℝ (threeCoupled r (4*m+1) ∘ (chartAt ThreeModel (threeMeridian c)).symm) 0
      (threeCircleDirection (threeMeridian c)) ≠ 0 := by
  rw [threeCoupled_circle_direction r (4*m+1) (by omega),threeMeridian_complex]
  simp only [Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hc.1],hc.2⟩
  have hsin : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hk : (0:ℝ)<(4*m+1:ℕ) := by positivity
  exact mul_ne_zero (neg_ne_zero.mpr hk.ne') (neg_ne_zero.mpr (by positivity))
lemma exists_threeCoupled_gradient_rank (r : ℝ) (hr : 0<r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c ∈ Ioo 0 (Real.pi/2), Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled r (4*m+1) ((chartAt ThreeModel (threeMeridian c)).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
          (threeCoupled r (4*m+1)) ((chartAt ThreeModel (threeMeridian c)).symm y))) 0) := by
  obtain ⟨c,hc,hR⟩ := exists_threeMeridianEnergy_deriv r hr hr1 hm
  refine ⟨c,hc,?_⟩
  let e := chartAt ThreeModel (threeMeridian c)
  let u := threeCoupled r (4*m+1)
  let R := coordinateGradientPair threeBackgroundMetric u u
  have hu := threeCoupled_smooth r (4*m+1)
  have hRs := contMDiff_coordinateGradientPair hu hu threeBackgroundMetric
  have ht : (0:ThreeModel) ∈ e.target := by rw [three_chart_target]; trivial
  have hud := (contDiffAt_inChart hu (threeMeridian c) ht).differentiableAt (by simp)
  have hRd := (contDiffAt_inChart hRs (threeMeridian c) ht).differentiableAt (by simp)
  change Function.Surjective (fderiv ℝ (fun y => ((u ∘ e.symm) y,(R ∘ e.symm) y)) 0)
  rw [hud.fderiv_prodMk hRd]
  apply linear_prod_surjective_of_directions _ _ (threeCircleDirection (threeMeridian c))
    (deriv (e ∘ threeMeridian) c)
  · exact threeMeridian_circle_deriv_ne r hr m hc
  · have hh := inChart_deriv_curve threeMeridian_smooth hu c
    rw [three_chart_center] at hh
    have hz : u ∘ threeMeridian = fun _ => 0 := funext (fun t => threeMeridian_zero r t m)
    change fderiv ℝ (u ∘ e.symm) 0 (deriv (e ∘ threeMeridian) c)=deriv (u ∘ threeMeridian) c at hh
    simpa only [hz,deriv_const] using hh
  · have hh := inChart_deriv_curve threeMeridian_smooth hRs c
    rw [three_chart_center] at hh
    exact hh.trans_ne hR
end YauCounterexamples
end

end OAI
