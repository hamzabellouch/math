import OAI.Analysis.CircleDomains.Topology.HolomorphicHomeomorph
import Mathlib.Analysis.Complex.OpenMapping

namespace OAI

/-! The local inverse of a holomorphic injection on an open plane set.
The inverse is first continuous by open mapping; isolated possible
critical values are removable. Thus its actual derivative is nonzero. -/
open Set Filter Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma injOn_not_eventually_constant {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hi : InjOn F U) {z : ℂ} (hz : z ∈ U) :
    ¬ ∀ᶠ w in 𝓝 z, F w = F z := by
  intro hc
  have hUz : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  have hf : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [hUz.filter_mono nhdsWithin_le_nhds,
      hc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw he hne
    exact hne (hi hw hz he)
  obtain ⟨w, hw⟩ := Filter.Eventually.exists hf
  exact hw

lemma holomorphicInjOn_map_nhds {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : map F (𝓝 z) = 𝓝 (F z) := by
  apply le_antisymm
  · exact ((hF z hz).differentiableAt (hU.mem_nhds hz)).continuousAt
  · exact (hF.analyticAt (hU.mem_nhds hz)).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (injOn_not_eventually_constant hU hi hz)

lemma continuousAt_holomorphic_invFunOn {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : ContinuousAt (invFunOn F U) (F z) := by
  have he : (invFunOn F U ∘ F) =ᶠ[𝓝 z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hi.leftInvOn_invFunOn hw
  change map (invFunOn F U) (𝓝 (F z)) ≤ 𝓝 (invFunOn F U (F z))
  rw [hi.leftInvOn_invFunOn hz, ← holomorphicInjOn_map_nhds hU hF hi hz,
    map_map, map_congr he, map_id]

lemma holomorphicInjOn_deriv_not_eventually_zero {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, deriv F w = 0 := by
  intro hzero
  have hUz : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (hUz.and hzero)
  have hsub : ball z r ⊆ U := fun w hw => (hb (by simpa only [mem_ball] using hw)).1
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z r).isPreconnected (hF.mono hsub)
    (fun w hw => (hb (by simpa only [mem_ball] using hw)).2)
  apply injOn_not_eventually_constant hU hi hz
  filter_upwards [ball_mem_nhds z hr] with w hw
  exact (hc w hw).trans (hc z (mem_ball_self hr)).symm

lemma holomorphicInjOn_inverse_differentiableAt {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ (invFunOn F U) (F z) := by
  let g := invFunOn F U
  have hgc : ContinuousAt g (F z) := continuousAt_holomorphic_invFunOn hU hF hi hz
  have hgz : g (F z) = z := hi.leftInvOn_invFunOn hz
  have ha := hF.analyticAt (hU.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, deriv F w ≠ 0 :=
    ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (holomorphicInjOn_deriv_not_eventually_zero hU hF hi hz)
  have hgc' : Tendsto g (𝓝 (F z)) (𝓝 z) := by
    change Tendsto g (𝓝 (F z)) (𝓝 (g (F z))) at hgc
    simpa only [hgz] using hgc
  have himage : ∀ᶠ y in 𝓝 (F z), y ∈ F '' U := by
    rw [← holomorphicInjOn_map_nhds hU hF hi hz]
    exact image_mem_map (hU.mem_nhds hz)
  have hgun : ∀ᶠ y in 𝓝 (F z), g y ∈ U := by
    filter_upwards [himage] with y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change invFunOn F U (F x) ∈ U
    rw [hi.leftInvOn_invFunOn hx]
    exact hx
  have ht : Tendsto g (𝓝[≠] (F z)) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hgc'.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [himage.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hne
    intro hgy
    have hright : F (g y) = y := invFunOn_eq hy
    rw [hgy] at hright
    exact hne hright.symm
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ hgc).differentiableAt
  filter_upwards [ht.eventually hn, hgun.filter_mono nhdsWithin_le_nhds,
    himage.filter_mono nhdsWithin_le_nhds] with y hy hyU hyimage
  have hcont : ContDiffAt ℂ 1 F (g y) := (hF.analyticAt (hU.mem_nhds hyU)).contDiffAt
  have hs := hcont.hasStrictDerivAt'
    ((hF _ hyU).differentiableAt (hU.mem_nhds hyU)).hasDerivAt (by norm_num)
  have hleft : (g ∘ F) =ᶠ[𝓝 (g y)] id := by
    filter_upwards [hU.mem_nhds hyU] with w hw
    exact hi.leftInvOn_invFunOn hw
  have hd := (hs.to_local_left_inverse hy hleft).hasDerivAt.differentiableAt
  rw [show F (g y) = y from invFunOn_eq hyimage] at hd
  exact hd

lemma holomorphicInjOn_deriv_ne_zero {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hi : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : deriv F z ≠ 0 := by
  have hf := ((hF z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hg := (holomorphicInjOn_inverse_differentiableAt hU hF hi hz).hasDerivAt
  have hleft : (invFunOn F U ∘ F) =ᶠ[𝓝 z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hi.leftInvOn_invFunOn hw
  have hd := (hg.comp z hf).congr_of_eventuallyEq hleft.symm
  have he := hd.deriv
  rw [deriv_id] at he
  intro hzero
  rw [hzero, mul_zero] at he
  exact one_ne_zero he

end CircleDomainRigidity

end

end OAI
