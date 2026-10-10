import OAI.Analysis.CircleDomains.Reflection.SemidiskModulusExtension
import OAI.Analysis.CircleDomains.Reflection.CircleSchwarzReflection

namespace OAI

/-! A bounded holomorphic disk-valued map with modulus tending to one
at a straight boundary has an actual holomorphic continuation there.
Complex boundary continuity is constructed, rather than assumed. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma exists_holomorphic_continuation_of_modulus_trace {R c : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hc : 0<c) (hc1 : c≤1)
    (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hlower : ∀z∈upperSemidisk R,c≤‖f z‖)
    (hupper : ∀z∈upperSemidisk R,‖f z‖<1)
    (htrace : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 1)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 (R/4) ∧
      DifferentiableOn ℂ F V ∧ EqOn F f (V∩{z : ℂ | 0<z.im}) := by
  obtain ⟨F,hFc,hFeq,hFn⟩ := exists_continuous_extension_of_modulus_trace
    hR hc hc1 hd hlower hupper htrace
  have hFn0 : ‖F 0‖=1 := hFn 0 (by simpa using (show 0<R/4 by positivity)) (by simp)
  let a : ℂ := -conj (F 0)
  have ha : ‖a‖=1 := by simpa only [a,norm_neg,norm_conj] using hFn0
  have ha0 : a≠0 := norm_ne_zero_iff.mp (by rw [ha];norm_num)
  have hval : a*F 0 = -1 := by
    dsimp only [a]
    rw [neg_mul,←normSq_eq_conj_mul_self,normSq_eq_norm_sq,hFn0]
    norm_num
  let q : ℂ → ℂ := fun z => a*F z
  have hqc : Continuous q := continuous_const.mul hFc
  have hq0 : q 0≠1 := by change a*F 0≠1;rw [hval];norm_num
  have hnb : ball (0:ℂ) (R/4)∩{z : ℂ | q z≠1} ∈ 𝓝 (0:ℂ) :=
    inter_mem (ball_mem_nhds _ (by positivity))
      (hqc.continuousAt.eventually (isOpen_ne.mem_nhds hq0))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hnb
  let U := ball (0:ℂ) r
  have hU : IsOpen U := isOpen_ball
  have hs : ∀z∈U,conj z∈U := by
    intro z hz
    simpa only [U,mem_ball_zero_iff,norm_conj] using hz
  have hqd : ∀z∈U,0<z.im → DifferentiableAt ℂ q z := by
    intro z hz hz0
    have hzS : z∈upperSemidisk (R/4) := ⟨(hrsub hz).1,hz0⟩
    have heq : F =ᶠ[𝓝 z] f := by
      filter_upwards [(upperSemidisk_open (R/4)).mem_nhds hzS] with w hw
      exact hFeq hw
    have hzR := upperSemidisk_mono (by linarith : R/4≤R) hzS
    exact (heq.differentiableAt_iff.mpr
      ((hd z hzR).differentiableAt ((upperSemidisk_open R).mem_nhds hzR))).const_mul a
  have hqr : ∀z∈U,z.im=0 → ‖q z‖=1 := by
    intro z hz hz0
    change ‖a*F z‖=1
    rw [norm_mul,ha,hFn z (mem_ball_zero_iff.mp (hrsub hz).1) hz0,one_mul]
  have hqp : ∀z∈U,0≤z.im → q z≠1 := fun z hz _ => (hrsub hz).2
  obtain ⟨V,H,hV,h0,hVU,hHd,hHeq⟩ := exists_local_circle_reflection hU hs hqc.continuousOn
    hqd hqr hqp (mem_ball_self hr) (by simp)
  refine ⟨V,fun z => a⁻¹*H z,hV,h0,fun z hz => (hrsub (hVU hz)).1,
    hHd.const_mul _,?_⟩
  intro z hz
  change a⁻¹*H z=f z
  rw [hHeq ⟨hz.1,(show 0<z.im from hz.2).le⟩]
  change a⁻¹*(a*F z)=f z
  rw [←mul_assoc,inv_mul_cancel₀ ha0,one_mul]
  exact hFeq ⟨(hrsub (hVU hz.1)).1,hz.2⟩

end CircleDomainRigidity

end

end OAI
