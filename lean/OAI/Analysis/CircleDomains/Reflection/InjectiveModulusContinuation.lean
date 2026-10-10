import OAI.Analysis.CircleDomains.Topology.ContinuationBoundaryValues
import OAI.Analysis.CircleDomains.Reflection.InjectiveCircleReflectionSides

namespace OAI

/-! The actual boundary continuation is locally injective and has no
critical boundary point when the original upper-side map is injective. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma exists_injective_continuation_of_modulus_trace_sides {R : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hi : InjOn f (upperSemidisk R)) (hu : ∀z∈upperSemidisk R,‖f z‖<1)
    (ht : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 1)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F f (V∩{z:ℂ | 0<z.im}) ∧ (∀z∈V,deriv F z≠0) ∧
      ∀z∈V,‖F z‖<1 ↔ 0<z.im := by
  obtain ⟨V₀,F₀,hV₀,h00,hV₀R,hF₀d,hF₀e⟩ :=
    exists_local_holomorphic_continuation_of_modulus_trace hR hd hu ht
  have hF₀r : ∀z∈V₀,z.im=0 → ‖F₀ z‖=1 :=
    fun z hz hz0 => norm_eq_one_on_real_continuation hV₀ hV₀R hF₀d.continuousOn hF₀e ht hz hz0
  have hn0 : ‖F₀ 0‖=1 := hF₀r 0 h00 (by simp)
  let a : ℂ := -conj (F₀ 0)
  have ha : ‖a‖=1 := by simpa only [a,norm_neg,norm_conj] using hn0
  have ha0 : a≠0 := norm_ne_zero_iff.mp (by rw [ha];norm_num)
  have hval : a*F₀ 0 = -1 := by
    dsimp only [a]
    rw [neg_mul,←normSq_eq_conj_mul_self,normSq_eq_norm_sq,hn0]
    norm_num
  let q : ℂ → ℂ := fun z => a*F₀ z
  have hqc : ContinuousAt q 0 := ((hF₀d 0 h00).differentiableAt (hV₀.mem_nhds h00)).continuousAt.const_mul a
  have hq0 : q 0≠1 := by change a*F₀ 0≠1;rw [hval];norm_num
  have hnb : V₀∩{z:ℂ | q z≠1} ∈ 𝓝 (0:ℂ) :=
    inter_mem (hV₀.mem_nhds h00) (hqc.eventually (isOpen_ne.mem_nhds hq0))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hnb
  let U := ball (0:ℂ) r
  have hU : IsOpen U := isOpen_ball
  have hs : ∀z∈U,conj z∈U := by
    intro z hz
    simpa only [U,mem_ball_zero_iff,norm_conj] using hz
  have hqcont : ContinuousOn q (U∩{z:ℂ | 0≤z.im}) :=
    (hF₀d.continuousOn.mono (fun _ hz => (hrsub hz.1).1)).const_mul a
  have hqd : ∀z∈U,0<z.im → DifferentiableAt ℂ q z := by
    intro z hz _
    exact ((hF₀d z (hrsub hz).1).differentiableAt (hV₀.mem_nhds (hrsub hz).1)).const_mul a
  have hqr : ∀z∈U,z.im=0 → ‖q z‖=1 := by
    intro z hz hz0
    change ‖a*F₀ z‖=1
    rw [norm_mul,ha,hF₀r z (hrsub hz).1 hz0,one_mul]
  have hqp : ∀z∈U,0≤z.im → q z≠1 := fun z hz _ => (hrsub hz).2
  have hzi : ∀z∈U,0<z.im → z∈upperSemidisk R :=
    fun z hz hz0 => ⟨hV₀R (hrsub hz).1,hz0⟩
  have hqu : ∀z∈U,0<z.im → ‖q z‖<1 := by
    intro z hz hz0
    change ‖a*F₀ z‖<1
    rw [norm_mul,ha,one_mul,hF₀e ⟨(hrsub hz).1,hz0⟩]
    exact hu z (hzi z hz hz0)
  have hqi : InjOn q (U∩{z:ℂ | 0<z.im}) := by
    intro z hz w hw he
    have hzw : F₀ z=F₀ w := mul_left_cancel₀ ha0 he
    rw [hF₀e ⟨(hrsub hz.1).1,hz.2⟩,hF₀e ⟨(hrsub hw.1).1,hw.2⟩] at hzw
    exact hi (hzi z hz.1 hz.2) (hzi w hw.1 hw.2) hzw
  obtain ⟨V,H,hV,h0,hVU,hHd,hHi,hHe,hHsides⟩ := exists_local_injective_circle_reflection_sides
    hU hs hqcont hqd hqi hqu hqr hqp (mem_ball_self hr) (by simp)
  let F : ℂ → ℂ := fun z => a⁻¹*H z
  have hFd : DifferentiableOn ℂ F V := hHd.const_mul _
  have hFi : InjOn F V := by
    intro z hz w hw he
    exact hHi hz hw (mul_left_cancel₀ (inv_ne_zero ha0) he)
  refine ⟨V,F,hV,h0,fun z hz => hV₀R (hrsub (hVU hz)).1,hFd,hFi,?_,
    fun z hz => holomorphicInjOn_deriv_ne_zero hV hFd hFi hz,?_⟩
  · intro z hz
    change a⁻¹*H z=f z
    rw [hHe ⟨hz.1,(show 0<z.im from hz.2).le⟩]
    change a⁻¹*(a*F₀ z)=f z
    rw [←mul_assoc,inv_mul_cancel₀ ha0,one_mul]
    exact hF₀e ⟨(hrsub (hVU hz.1)).1,hz.2⟩
  · intro z hz
    change ‖a⁻¹*H z‖<1 ↔ 0<z.im
    rw [norm_mul,norm_inv,ha,inv_one,one_mul]
    exact hHsides z hz

lemma exists_injective_continuation_of_modulus_trace {R : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hi : InjOn f (upperSemidisk R)) (hu : ∀z∈upperSemidisk R,‖f z‖<1)
    (ht : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 1)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F f (V∩{z:ℂ | 0<z.im}) ∧ ∀z∈V,deriv F z≠0 := by
  obtain ⟨V,F,hV,h0,hVR,hFd,hFi,hFe,hFn,_⟩ :=
    exists_injective_continuation_of_modulus_trace_sides hR hd hi hu ht
  exact ⟨V,F,hV,h0,hVR,hFd,hFi,hFe,hFn⟩

end CircleDomainRigidity

end

end OAI
