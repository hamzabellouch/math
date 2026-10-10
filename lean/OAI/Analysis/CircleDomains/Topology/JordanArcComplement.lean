import OAI.Analysis.CircleDomains.Selection.OuterContours

namespace OAI

/-! A proper subset of a Jordan curve does not separate the plane.
The proof joins the inside and outside through one omitted radial ray. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem isConnected_compl_subset_unit_circle {S : Set ℂ}
    (hS : S ⊆ Metric.sphere 0 1) {a : ℂ} (ha : ‖a‖ = 1) (haS : a ∉ S) :
    IsConnected Sᶜ := by
  let L : Set ℂ := (fun r : ℝ => r • a) '' Ici 0
  let T : Set ℂ := (Metric.ball (0 : ℂ) 1 ∪ L) ∪ (Metric.closedBall (0 : ℂ) 1)ᶜ
  have hL : IsPreconnected L := isPreconnected_Ici.image _
    (continuous_id.smul continuous_const).continuousOn
  have h0L : (0 : ℂ) ∈ L := ⟨(0 : ℝ), by simp, zero_smul _ _⟩
  have h2L : (2 : ℝ) • a ∈ L := ⟨2, by norm_num, rfl⟩
  have h2 : (2 : ℝ) • a ∈ (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ha]
    norm_num
  have hext : IsPreconnected (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    simpa only [jordanInterior, Homeomorph.refl_apply, image_id,
      closure_ball _ one_ne_zero] using
      (isConnected_exterior_jordanInterior (Homeomorph.refl ℂ)).isPreconnected
  have hT : IsPreconnected T :=
    (((Metric.isConnected_ball zero_lt_one).isPreconnected).union 0
      (Metric.mem_ball_self zero_lt_one) h0L hL).union ((2 : ℝ) • a)
        (Or.inr h2L) h2 hext
  have hTS : T ⊆ Sᶜ := by
    intro z hz hzS
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hS hzS)
    rcases hz with (hz | ⟨r, hr, rfl⟩) | hz
    · have hl : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      exact (ne_of_lt hl) hn
    · have hr1 : r = 1 := by
        have hr' : (0 : ℝ) ≤ r := hr
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr', ha, mul_one] using hn
      apply haS
      simpa only [hr1, one_smul] using hzS
    · exact hz (Metric.mem_closedBall.mpr (by simp only [dist_zero_right, hn, le_refl]))
  have hcl : Sᶜ ⊆ closure T := by
    intro z _
    by_cases hz : ‖z‖ ≤ 1
    · have hzcl : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
        rw [closure_ball _ one_ne_zero]
        exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz)
      exact closure_mono (fun _ h => Or.inl (Or.inl h)) hzcl
    · apply subset_closure
      right
      intro h
      exact hz (by simpa only [Metric.mem_closedBall, dist_zero_right] using h)
  exact ⟨⟨0, hTS (Or.inl (Or.inr h0L))⟩, hT.subset_closure hTS hcl⟩

theorem isConnected_compl_proper_jordan_subset (H : ℂ ≃ₜ ℂ) {S : Set ℂ}
    (hS : S ⊆ frontier (jordanInterior H))
    (hproper : ∃ a ∈ frontier (jordanInterior H), a ∉ S) :
    IsConnected Sᶜ := by
  obtain ⟨a, ha, haS⟩ := hproper
  have hpre : H ⁻¹' S ⊆ Metric.sphere 0 1 := by
    intro z hz
    have hf := hS hz
    rw [frontier_jordanInterior] at hf
    obtain ⟨w, hw, he⟩ := hf
    exact H.injective he ▸ hw
  have han : ‖H.symm a‖ = 1 := by
    rw [frontier_jordanInterior] at ha
    obtain ⟨z, hz, rfl⟩ := ha
    simpa only [H.symm_apply_apply] using mem_sphere_zero_iff_norm.mp hz
  have haS' : H.symm a ∉ H ⁻¹' S := by simpa only [mem_preimage, H.apply_symm_apply] using haS
  have hc := isConnected_compl_subset_unit_circle hpre han haS'
  have he : H '' (H ⁻¹' S)ᶜ = Sᶜ := by
    rw [H.image_compl, H.image_preimage]
  exact he ▸ hc.image H H.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
