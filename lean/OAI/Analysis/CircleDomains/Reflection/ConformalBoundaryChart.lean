import OAI.Analysis.CircleDomains.Topology.ConformalBoundaryApproach
import OAI.Analysis.CircleDomains.Reflection.LocalModulusContinuation
import OAI.Analysis.CircleDomains.Uniformization.ConformalLocalInverse

namespace OAI

/-! Apply the constructed modulus continuation to an actual conformal
map in a holomorphic boundary chart. No boundary values of the conformal
map are assumed. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma conformal_disk_boundary_chart_data {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U (((↑) : ℂ → Sphere) '' ball (0:ℂ) 1))
    (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    DifferentiableOn ℂ (fun z => finiteCoord (f (κ z : Sphere))) (upperSemidisk R) ∧
      (∀z∈upperSemidisk R,‖finiteCoord (f (κ z : Sphere))‖<1) ∧
      ∀p:ℂ,‖p‖≤R → p.im=0 →
        Tendsto (fun z => ‖finiteCoord (f (κ z : Sphere))‖)
          (𝓝[upperSemidisk R] p) (𝓝 1) := by
  let g : ℂ → ℂ := fun z => finiteCoord (f (κ z : Sphere))
  have hu : ∀z∈upperSemidisk R,‖g z‖<1 := by
    intro z hz
    obtain ⟨w,hw,he⟩ := hf.2.1 (hm z hz)
    change ‖finiteCoord (f (κ z : Sphere))‖<1
    rw [←he,finiteCoord_coe]
    exact mem_ball_zero_iff.mp hw
  have hd : DifferentiableOn ℂ g (upperSemidisk R) := by
    intro z hz
    have hn : f (κ z : Sphere)≠∞ := by
      obtain ⟨w,_,he⟩ := hf.2.1 (hm z hz)
      rw [←he]
      exact OnePoint.coe_ne_infty w
    have ha := analyticAt_finite_map_of_conformal hU hf.1 (hm z hz) hn
    exact (ha.differentiableAt.comp z
      ((hκ z hz).differentiableAt ((upperSemidisk_open R).mem_nhds hz))).differentiableWithinAt
  have ht : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖g z‖) (𝓝[upperSemidisk R] p) (𝓝 1) := by
    intro p hp hp0
    have hcp : Tendsto (fun z : ℂ => (κ z : Sphere))
        (𝓝[upperSemidisk R] p) (𝓝[U] (κ p : Sphere)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(OnePoint.continuous_coe.continuousAt.comp (hc p hp hp0)).tendsto.mono_left
        nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hm z hz
    have hft := hf.tendsto_disk_boundary_modulus zero_lt_one (hb p hp hp0)
    simpa only [Function.comp_def,sub_zero] using hft.comp hcp
  exact ⟨hd,hu,ht⟩

lemma conformal_disk_boundary_chart_continuation {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U (((↑) : ℂ → Sphere) '' ball (0:ℂ) 1))
    (hR : 0<R) (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧
      EqOn F (fun z => finiteCoord (f (κ z : Sphere))) (V∩{z : ℂ | 0<z.im}) := by
  obtain ⟨hd,hu,ht⟩ := conformal_disk_boundary_chart_data hU hf hκ hm hc hb
  exact exists_local_holomorphic_continuation_of_modulus_trace hR hd hu ht

end CircleDomainRigidity

end

end OAI
