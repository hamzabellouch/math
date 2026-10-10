import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative
import Mathlib.Analysis.Complex.AbsMax

namespace OAI

/-! A holomorphic injection cannot attain a positive lower modulus bound,
or any upper modulus bound, in the interior. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma holomorphicInjOn_norm_gt {U:Set ℂ} {f:ℂ→ℂ} {c:ℂ} {r:ℝ}
    (hU:IsOpen U) (hd:DifferentiableOn ℂ f U) (hi:InjOn f U)
    (hr:0<r) (hb:∀z∈U,r≤‖f z-c‖) {z:ℂ} (hz:z∈U) : r<‖f z-c‖ := by
  apply lt_of_le_of_ne (hb z hz)
  intro he
  have hdiff : ∀ᶠw in 𝓝 z,DifferentiableAt ℂ (fun v => f v-c) w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact ((hd w hw).differentiableAt (hU.mem_nhds hw)).sub_const c
  have hmin : IsLocalMin (norm ∘ fun v => f v-c) z := by
    filter_upwards [hU.mem_nhds hz] with w hw
    change ‖f z-c‖≤‖f w-c‖
    rw [←he]
    exact hb w hw
  rcases Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm hdiff hmin with hc|hc
  · apply injOn_not_eventually_constant hU hi hz
    exact hc.mono (fun w hw => sub_left_injective hw)
  · have hzero : ‖f z-c‖=0 := by rw [hc,norm_zero]
    linarith

lemma holomorphicInjOn_norm_lt {U:Set ℂ} {f:ℂ→ℂ} {c:ℂ} {r:ℝ}
    (hU:IsOpen U) (hd:DifferentiableOn ℂ f U) (hi:InjOn f U)
    (hb:∀z∈U,‖f z-c‖≤r) {z:ℂ} (hz:z∈U) : ‖f z-c‖<r := by
  apply lt_of_le_of_ne (hb z hz)
  intro he
  have hdiff : ∀ᶠw in 𝓝 z,DifferentiableAt ℂ (fun v => f v-c) w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact ((hd w hw).differentiableAt (hU.mem_nhds hw)).sub_const c
  have hmax : IsLocalMax (norm ∘ fun v => f v-c) z := by
    filter_upwards [hU.mem_nhds hz] with w hw
    change ‖f w-c‖≤‖f z-c‖
    rw [he]
    exact hb w hw
  have hc := Complex.eventually_eq_of_isLocalMax_norm hdiff hmax
  apply injOn_not_eventually_constant hU hi hz
  exact hc.mono (fun w hw => sub_left_injective hw)

end CircleDomainRigidity

end

end OAI
