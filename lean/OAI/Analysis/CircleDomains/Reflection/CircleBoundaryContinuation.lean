import OAI.Analysis.CircleDomains.Reflection.CircleSchwarzReflection

namespace OAI

/-! A map continuous up to a circular boundary and taking that boundary
to a circle extends holomorphically near each finite Cayley chart point.
Both coordinate changes and the extension are constructed explicitly. -/
open Set Function Metric Filter Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma exists_unit_circle_continuation {W : Set ℂ} {f : ℂ → ℂ}
    (hW : IsOpen W)
    (hc : ContinuousOn f (W∩closedBall (0 : ℂ) 1))
    (hd : ∀z∈W,‖z‖<1 → DifferentiableAt ℂ f z)
    (hr : ∀z∈W,‖z‖=1 → ‖f z‖=1)
    (hpole : ∀z∈W,‖z‖≤1 → f z≠1)
    {p : ℂ} (hp : p∈W) (hpn : ‖p‖=1) (hp1 : p≠1) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ p∈V ∧ V⊆W ∧
      DifferentiableOn ℂ F V ∧ EqOn F f (V∩closedBall (0 : ℂ) 1) := by
  let a := diskHalfPlane p
  have ha0 : a.im=0 := diskHalfPlane_real hp1 hpn
  have had : a+I≠0 := diskHalfPlane_add_I_ne_zero hp1
  have haW : halfPlaneDisk a∈W := by
    rw [halfPlaneDisk_diskHalfPlane hp1]
    exact hp
  have hnhds : {z : ℂ | halfPlaneDisk z∈W}∩{z : ℂ | z+I≠0} ∈ 𝓝 a := by
    exact inter_mem ((differentiableAt_halfPlaneDisk had).continuousAt.eventually
      (hW.mem_nhds haW))
      ((continuousAt_id.add_const I).eventually
        ((isOpen_ne).mem_nhds had))
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let U := ball a ε
  have hU : IsOpen U := isOpen_ball
  have hsym : ∀z∈U,conj z∈U := by
    intro z hz
    have hac : conj a=a := conj_eq_iff_im.mpr ha0
    change dist (conj z) a<ε
    rw [dist_conj_comm,hac]
    exact hz
  let g : ℂ → ℂ := fun z => f (halfPlaneDisk z)
  have hgc : ContinuousOn g (U∩{z : ℂ | 0≤z.im}) := by
    have ht : ContinuousOn halfPlaneDisk U := fun z hz =>
      (differentiableAt_halfPlaneDisk (hεsub hz).2).continuousAt.continuousWithinAt
    apply hc.comp (ht.mono inter_subset_left)
    intro z hz
    exact ⟨(hεsub hz.1).1,mem_closedBall_zero_iff.mpr (halfPlaneDisk_norm_le hz.2)⟩
  have hgd : ∀z∈U,0<z.im → DifferentiableAt ℂ g z := by
    intro z hz hz0
    exact (hd _ (hεsub hz).1 (halfPlaneDisk_norm_lt hz0)).comp z
      (differentiableAt_halfPlaneDisk (hεsub hz).2)
  have hgr : ∀z∈U,z.im=0 → ‖g z‖=1 := by
    intro z hz hz0
    exact hr _ (hεsub hz).1 (halfPlaneDisk_norm_eq hz0)
  have hgp : ∀z∈U,0≤z.im → g z≠1 := by
    intro z hz hz0
    exact hpole _ (hεsub hz).1 (halfPlaneDisk_norm_le hz0)
  obtain ⟨A,H,hA,haA,hAU,hH,hHeq⟩ := exists_local_circle_reflection hU hsym hgc hgd hgr hgp
    (mem_ball_self hε) ha0
  have hpre : W∩{z : ℂ | z≠1}∩{z : ℂ | diskHalfPlane z∈A} ∈ 𝓝 p := by
    exact inter_mem
      (inter_mem (hW.mem_nhds hp) ((isOpen_ne).mem_nhds hp1))
      ((differentiableAt_diskHalfPlane hp1).continuousAt.eventually (hA.mem_nhds haA))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ball p δ,fun z => H (diskHalfPlane z),isOpen_ball,mem_ball_self hδ,
    fun z hz => (hδsub hz).1.1,?_,?_⟩
  · intro z hz
    exact (((hH _ (hδsub hz).2).differentiableAt (hA.mem_nhds (hδsub hz).2)).comp z
      (differentiableAt_diskHalfPlane (hδsub hz).1.2)).differentiableWithinAt
  · intro z hz
    change H (diskHalfPlane z)=f z
    rw [hHeq ⟨(hδsub hz.1).2,
      diskHalfPlane_nonneg (hδsub hz.1).1.2 (mem_closedBall_zero_iff.mp hz.2)⟩]
    change f (halfPlaneDisk (diskHalfPlane z))=f z
    rw [halfPlaneDisk_diskHalfPlane (hδsub hz.1).1.2]

end CircleDomainRigidity

end

end OAI
