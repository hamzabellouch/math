import OAI.Analysis.CircleDomains.Reflection.SchwarzReflectionInteriorInjectivity
import OAI.Analysis.CircleDomains.Reflection.CayleySides

namespace OAI

/-! The circle continuation is injective from interior injectivity alone.
No boundary injectivity or nonzero boundary derivative is assumed. -/
open Set Function Metric Filter Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma exists_local_injective_circle_reflection_sides {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hi : InjOn f (U∩{z : ℂ | 0<z.im}))
    (hinside : ∀z∈U,0<z.im → ‖f z‖<1)
    (hcircle : ∀z∈U,z.im=0 → ‖f z‖=1)
    (hpole : ∀z∈U,0≤z.im → f z≠1)
    {a : ℂ} (ha : a∈U) (ha0 : a.im=0) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ a∈V ∧ V⊆U ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧ EqOn F f (V∩{z : ℂ | 0≤z.im}) ∧
      ∀z∈V, ‖F z‖<1 ↔ 0<z.im := by
  let g : ℂ → ℂ := fun z => diskHalfPlane (f z)
  have hgc : ContinuousOn g (U∩{z : ℂ | 0≤z.im}) :=
    continuousOn_diskHalfPlane.comp hc (fun z hz => hpole z hz.1 hz.2)
  have hgd : ∀z∈U,0<z.im → DifferentiableAt ℂ g z := by
    intro z hz hz0
    exact (differentiableAt_diskHalfPlane (hpole z hz hz0.le)).comp z (hd z hz hz0)
  have hgr : ∀z∈U,z.im=0 → (g z).im=0 := by
    intro z hz hz0
    exact diskHalfPlane_real (hpole z hz hz0.ge) (hcircle z hz hz0)
  have hgi : InjOn g (U∩{z : ℂ | 0<z.im}) := by
    intro z hz w hw he
    apply hi hz hw
    exact diskHalfPlane_injOn_nonpole (hpole z hz.1 (show 0<z.im from hz.2).le)
      (hpole w hw.1 (show 0<w.im from hw.2).le) he
  have hgp : ∀z∈U,0<z.im → 0<(g z).im :=
    fun z hz hz0 => diskHalfPlane_pos (hinside z hz hz0)
  let H := schwarzReflect g
  have hHi : InjOn H U := injOn_schwarzReflect_of_injOn_upper hU hs hgc hgd hgi hgr hgp
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
    fun z hz => (hball hz).1,?_,?_,?_,?_⟩
  · intro z hz
    exact ((differentiableAt_halfPlaneDisk (hball hz).2).comp z
      ((hHd z (hball hz).1).differentiableAt (hU.mem_nhds (hball hz).1))).differentiableWithinAt
  · intro z hz w hw he
    apply hHi (hball hz).1 (hball hw).1
    exact halfPlaneDisk_injOn_nonpole (hball hz).2 (hball hw).2 he
  · intro z hz
    change halfPlaneDisk (schwarzReflect g z)=f z
    rw [schwarzReflect_eq hz.2]
    exact halfPlaneDisk_diskHalfPlane (hpole z (hball hz.1).1 hz.2)

  · intro z hz
    rw [halfPlaneDisk_norm_lt_iff (hball hz).2]
    exact schwarzReflect_strict_upper_iff hs hgr hgp (hball hz).1

end CircleDomainRigidity

end

end OAI
