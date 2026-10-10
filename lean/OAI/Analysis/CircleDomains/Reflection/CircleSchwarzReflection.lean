import OAI.Analysis.CircleDomains.Reflection.SchwarzReflectionInjective
import OAI.Analysis.CircleDomains.Reflection.CayleyHolomorphic

namespace OAI

/-! Local holomorphic continuation across a real interval whose image
lies on a circle. The continuation is constructed by Cayley coordinates
and the proved real-axis reflection principle. -/
open Set Function Metric Filter Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma exists_local_circle_reflection {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hcircle : ∀z∈U,z.im=0 → ‖f z‖=1)
    (hpole : ∀z∈U,0≤z.im → f z≠1)
    {a : ℂ} (ha : a∈U) (ha0 : a.im=0) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ a∈V ∧ V⊆U ∧
      DifferentiableOn ℂ F V ∧ EqOn F f (V∩{z : ℂ | 0≤z.im}) := by
  let g : ℂ → ℂ := fun z => diskHalfPlane (f z)
  have hgc : ContinuousOn g (U∩{z : ℂ | 0≤z.im}) :=
    continuousOn_diskHalfPlane.comp hc (fun z hz => hpole z hz.1 hz.2)
  have hgd : ∀z∈U,0<z.im → DifferentiableAt ℂ g z := by
    intro z hz hz0
    exact (differentiableAt_diskHalfPlane (hpole z hz hz0.le)).comp z (hd z hz hz0)
  have hgr : ∀z∈U,z.im=0 → (g z).im=0 := by
    intro z hz hz0
    exact diskHalfPlane_real (hpole z hz hz0.ge) (hcircle z hz hz0)
  let H := schwarzReflect g
  have hHc : ContinuousOn H U := continuousOn_schwarzReflect hs hgc hgr
  have hHd : DifferentiableOn ℂ H U := differentiableOn_schwarzReflect hU hs hgc hgd hgr
  have hHa : H a+I≠0 := by
    change schwarzReflect g a+I≠0
    rw [schwarzReflect_eq ha0.ge]
    exact diskHalfPlane_add_I_ne_zero (hpole a ha ha0.ge)
  have hnbhd : U∩{z : ℂ | H z+I≠0} ∈ 𝓝 a := by
    apply inter_mem (hU.mem_nhds ha)
    exact ((hHc.continuousAt (hU.mem_nhds ha)).add_const I).eventually
      (isOpen_ne |>.mem_nhds hHa)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  refine ⟨ball a ε,fun z => halfPlaneDisk (H z),isOpen_ball,mem_ball_self hε,
    fun z hz => (hball hz).1,?_,?_⟩
  · intro z hz
    exact ((differentiableAt_halfPlaneDisk (hball hz).2).comp z
      ((hHd z (hball hz).1).differentiableAt (hU.mem_nhds (hball hz).1))).differentiableWithinAt
  · intro z hz
    change halfPlaneDisk (schwarzReflect g z)=f z
    rw [schwarzReflect_eq hz.2]
    exact halfPlaneDisk_diskHalfPlane (hpole z (hball hz.1).1 hz.2)

end CircleDomainRigidity

end

end OAI
