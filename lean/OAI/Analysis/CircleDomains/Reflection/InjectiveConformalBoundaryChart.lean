import OAI.Analysis.CircleDomains.Reflection.ConformalBoundaryChart
import OAI.Analysis.CircleDomains.Reflection.InjectiveModulusContinuation
import OAI.Analysis.CircleDomains.Uniformization.ExteriorDiskNormalization

namespace OAI

/-! The actual conformal equivalence, in an injective source chart, has
an injective holomorphic continuation with nonzero boundary derivative. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma injective_conformal_disk_boundary_chart_sides {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U (((↑) : ℂ → Sphere) '' ball (0:ℂ) 1))
    (hR : 0<R) (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hi : InjOn κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F (fun z => finiteCoord (f (κ z : Sphere))) (V∩{z : ℂ | 0<z.im}) ∧
      (∀z∈V,deriv F z≠0) ∧ ∀z∈V,‖F z‖<1 ↔ 0<z.im := by
  obtain ⟨hd,hu,ht⟩ := conformal_disk_boundary_chart_data hU hf hκ hm hc hb
  have hgi : InjOn (fun z => finiteCoord (f (κ z : Sphere))) (upperSemidisk R) := by
    intro z hz w hw he
    apply hi hz hw
    apply OnePoint.coe_injective
    apply hf.bijOn.injOn (hm z hz) (hm w hw)
    obtain ⟨a,_,ha⟩ := hf.2.1 (hm z hz)
    obtain ⟨b,_,hb⟩ := hf.2.1 (hm w hw)
    change finiteCoord (f (κ z : Sphere))=finiteCoord (f (κ w : Sphere)) at he
    rw [←ha,←hb,finiteCoord_coe,finiteCoord_coe] at he
    rw [←ha,←hb,he]
  exact exists_injective_continuation_of_modulus_trace_sides hR hd hgi hu ht

lemma injective_conformal_disk_boundary_chart {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U (((↑) : ℂ → Sphere) '' ball (0:ℂ) 1))
    (hR : 0<R) (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hi : InjOn κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F (fun z => finiteCoord (f (κ z : Sphere))) (V∩{z : ℂ | 0<z.im}) ∧
      ∀z∈V,deriv F z≠0 := by
  obtain ⟨V,F,hV,h0,hVR,hFd,hFi,hFe,hFn,_⟩ :=
    injective_conformal_disk_boundary_chart_sides hU hf hR hκ hi hm hc hb
  exact ⟨V,F,hV,h0,hVR,hFd,hFi,hFe,hFn⟩

lemma injective_circular_exterior_boundary_chart_sides {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R r : ℝ} {c : ℂ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ))
    (hr : 0<r) (hR : 0<R) (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hi : InjOn κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F (fun z => finiteCoord (exteriorDiskNormalization c r hr (f (κ z : Sphere))))
        (V∩{z : ℂ | 0<z.im}) ∧ (∀z∈V,deriv F z≠0) ∧ ∀z∈V,‖F z‖<1 ↔ 0<z.im :=
  injective_conformal_disk_boundary_chart_sides hU
    (hf.trans (isConformalEquivalence_exteriorDiskNormalization c hr)) hR hκ hi hm hc hb

lemma injective_circular_exterior_boundary_chart {U : Set Sphere}
    {f : Sphere → Sphere} {κ : ℂ → ℂ} {R r : ℝ} {c : ℂ}
    (hU : IsOpen U)
    (hf : IsConformalEquivalence f U ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ))
    (hr : 0<r) (hR : 0<R) (hκ : DifferentiableOn ℂ κ (upperSemidisk R))
    (hi : InjOn κ (upperSemidisk R))
    (hm : ∀z∈upperSemidisk R,(κ z : Sphere)∈U)
    (hc : ∀p:ℂ,‖p‖≤R → p.im=0 → ContinuousAt κ p)
    (hb : ∀p:ℂ,‖p‖≤R → p.im=0 → (κ p : Sphere)∉U) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F (fun z => finiteCoord (exteriorDiskNormalization c r hr (f (κ z : Sphere))))
        (V∩{z : ℂ | 0<z.im}) ∧ ∀z∈V,deriv F z≠0 := by
  obtain ⟨V,F,hV,h0,hVR,hFd,hFi,hFe,hFn,_⟩ :=
    injective_circular_exterior_boundary_chart_sides hU hf hr hR hκ hi hm hc hb
  exact ⟨V,F,hV,h0,hVR,hFd,hFi,hFe,hFn⟩

end CircleDomainRigidity

end

end OAI
