import OAI.Analysis.CircleDomains.Reflection.ConformalChartTransport
import OAI.Analysis.CircleDomains.Reflection.RoundExteriorBoundaryInjectivity
import OAI.Analysis.CircleDomains.Reflection.CayleySides
import OAI.Analysis.CircleDomains.Reflection.HolomorphicAcrossRealAxis

namespace OAI

/-! A continuous function holomorphic off a circle is holomorphic across
that circle. The proof uses the explicit circle chart and the proved
real-axis gluing lemma. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma differentiableAt_of_comp_holomorphic_chart {κ f:ℂ→ℂ} {N:Set ℂ}
    (hN:IsOpen N) (h0:(0:ℂ)∈N) (hκ:DifferentiableOn ℂ κ N)
    (hi:InjOn κ N) (hf:DifferentiableAt ℂ (f ∘ κ) 0) :
    DifferentiableAt ℂ f (κ 0) := by
  have hinv : invFunOn κ N (κ 0)=0 := hi.leftInvOn_invFunOn h0
  have hfd : DifferentiableAt ℂ (f ∘ κ) (invFunOn κ N (κ 0)) := by
    rw [hinv]
    exact hf
  have hd := hfd.comp (κ 0) (holomorphicInjOn_inverse_differentiableAt hN hκ hi h0)
  have hnb : κ '' N∈𝓝 (κ 0) := by
    rw [←holomorphicInjOn_map_nhds hN hκ hi h0]
    exact image_mem_map (hN.mem_nhds h0)
  have he : (f ∘ κ) ∘ invFunOn κ N =ᶠ[𝓝 (κ 0)] f := by
    filter_upwards [hnb] with y hy
    obtain ⟨z,hz,rfl⟩ := hy
    simp only [Function.comp_apply,hi.leftInvOn_invFunOn hz]
  exact he.differentiableAt_iff.mp hd

lemma differentiableOn_of_continuousOn_off_unit_circle {U:Set ℂ} {f:ℂ→ℂ}
    (hU:IsOpen U) (hc:ContinuousOn f U)
    (hd:∀z∈U,‖z‖≠1→DifferentiableAt ℂ f z) : DifferentiableOn ℂ f U := by
  intro p hpU
  by_cases hp : ‖p‖=1
  · let κ := unitExteriorBoundaryChart p
    let N : Set ℂ := ball 0 1
    have hN : IsOpen N := isOpen_ball
    have h0N : (0:ℂ)∈N := mem_ball_self zero_lt_one
    have hκ : DifferentiableOn ℂ κ N :=
      fun z hz => (differentiableAt_unitExteriorBoundaryChart p (mem_ball_zero_iff.mp hz)).differentiableWithinAt
    have hi : InjOn κ N := unitExteriorBoundaryChart_injOn (norm_ne_zero_iff.mp (by rw [hp];norm_num))
    let V := N∩κ ⁻¹' U
    have hV : IsOpen V := hκ.continuousOn.isOpen_inter_preimage hN hU
    have h0V : (0:ℂ)∈V := ⟨h0N,by
      change κ 0∈U
      rwa [show κ 0=p from unitExteriorBoundaryChart_zero p]⟩
    have hfc : ContinuousOn (f ∘ κ) V :=
      hc.comp (hκ.continuousOn.mono inter_subset_left) (fun _ hz => hz.2)
    have hfd : DifferentiableOn ℂ (f ∘ κ) V := by
      apply differentiableOn_of_continuousOn_off_real hV hfc
      intro z hz hzi
      have hzn := mem_ball_zero_iff.mp hz.1
      have hneq : ‖κ z‖≠1 := by
        intro he
        change ‖unitExteriorBoundaryChart p z‖=1 at he
        rw [unitExteriorBoundaryChart,norm_div,norm_neg,hp] at he
        have hcay : ‖halfPlaneDisk z‖=1 :=
          ((div_eq_one_iff_eq (norm_ne_zero_iff.mpr (cayley_ne_zero_of_norm_lt_one hzn))).mp he).symm
        exact hzi ((halfPlaneDisk_norm_eq_iff (cayley_den_ne_zero_of_norm_lt_one hzn)).mp hcay)
      exact (hd (κ z) hz.2 hneq).comp z
        (differentiableAt_unitExteriorBoundaryChart p hzn)
    have hdp := differentiableAt_of_comp_holomorphic_chart hN h0N hκ hi
      ((hfd 0 h0V).differentiableAt (hV.mem_nhds h0V))
    rw [show κ 0=p from unitExteriorBoundaryChart_zero p] at hdp
    exact hdp.differentiableWithinAt
  · exact (hd p hpU hp).differentiableWithinAt

end CircleDomainRigidity

end

end OAI
