import Mathlib
import OAI.Analysis.Crouzeix.Univalent

namespace OAI

/-! Boundary Modulus. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

attribute [local instance] Classical.propDecidable

theorem isCompact_preimage_closedBall {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    {r : ℝ} (hr : r < 1) : IsCompact (U ∩ f ⁻¹' closedBall 0 r) := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr
  have hd : DifferentiableOn ℂ (invFunOn f U) (ball 0 1) :=
    fun w hw => (hasStrictDerivAt_invFunOn hU hf hbij hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have he : U ∩ f ⁻¹' closedBall 0 r = invFunOn f U '' closedBall 0 r := by
    ext z
    constructor
    · rintro ⟨hzu, hz⟩
      exact ⟨f z, hz, hbij.invOn_invFunOn.1 hzu⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(hbij.symm hbij.invOn_invFunOn.symm).mapsTo (hsub hw),
        by simpa only [mem_preimage, hbij.invOn_invFunOn.2 (hsub hw)] using hw⟩
  rw [he]
  exact (isCompact_closedBall 0 r).image_of_continuousOn (hd.continuousOn.mono hsub)

theorem tendsto_norm_one_at_frontier {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    {p : ℂ} (hp : p ∈ frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hK := isCompact_preimage_closedBall hU hf hbij (sub_lt_self (1 : ℝ) hε)
  have hpn : p ∉ U ∩ f ⁻¹' closedBall 0 (1 - ε) := by
    intro he
    exact hp.2 (hU.interior_eq.symm ▸ he.1)
  filter_upwards [Filter.mem_inf_of_left (hK.isClosed.isOpen_compl.mem_nhds hpn),
    self_mem_nhdsWithin] with z hz₁ hz₂
  have hsmall : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hbij.mapsTo hz₂)
  have hlarge : 1 - ε < ‖f z‖ := by
    by_contra h
    exact hz₁ ⟨hz₂, mem_closedBall_zero_iff.mpr (le_of_not_gt h)⟩
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem continuousOn_closed_modulus {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1)) :
    ContinuousOn (fun z => if z ∈ U then ‖f z‖ else 1) (closure U) := by
  classical
  intro p hp
  by_cases hpU : p ∈ U
  · apply (hf.continuousOn.norm.continuousAt (hU.mem_nhds hpU)).continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.mem_inf_of_left (hU.mem_nhds hpU)] with z hz
      simp only [ite_eq_left hz]
    · simp only [ite_eq_left hpU]
  · have hpf : p ∈ frontier U := ⟨hp, by simpa only [hU.interior_eq] using hpU⟩
    have ht := tendsto_norm_one_at_frontier hU hf hbij hpf
    rw [ContinuousWithinAt, ite_eq_right hpU]
    let : DecidablePred U := fun z => Classical.propDecidable _
    exact (ht.mono_left (nhdsWithin_mono p inter_subset_right)).if_nhdsWithin tendsto_const_nhds

end CrouzeixHilbert.Conformal

end

end OAI
