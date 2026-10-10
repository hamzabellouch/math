import OAI.Analysis.CircleDomains.Reflection.SemidiskLogarithm

namespace OAI

/-! Continuity at a boundary arc follows from convergence of the modulus
alone. The logarithm, the half-disk barrier and the derivative bound
supply the missing complex boundary values. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma mem_closure_upperSemidisk {R : ℝ} {p : ℂ} (hn : ‖p‖<R) (hi : 0≤p.im) :
    p∈closure (upperSemidisk R) := by
  have hp : p∈closure {z : ℂ | 0<z.im} := by
    rw [closure_setOfPred_lt_im]
    exact hi
  apply _root_.mem_closure_iff.mpr
  intro O hO hpO
  obtain ⟨w,hw,hwu⟩ := _root_.mem_closure_iff.mp hp (O∩ball 0 R) (hO.inter isOpen_ball)
    ⟨hpO,mem_ball_zero_iff.mpr hn⟩
  exact ⟨w,hw.1,hw.2,hwu⟩

lemma upperSemidisk_mono {R S : ℝ} (hRS : R≤S) : upperSemidisk R⊆upperSemidisk S :=
  fun _ hz => ⟨ball_subset_ball hRS hz.1,hz.2⟩

lemma exists_continuous_extension_of_modulus_trace {R c : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hc : 0<c) (hc1 : c≤1)
    (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hlower : ∀z∈upperSemidisk R,c≤‖f z‖)
    (hupper : ∀z∈upperSemidisk R,‖f z‖<1)
    (htrace : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 1)) :
    ∃F:ℂ→ℂ,Continuous F ∧ EqOn F f (upperSemidisk (R/4)) ∧
      ∀p:ℂ,‖p‖<R/4 → p.im=0 → ‖F p‖=1 := by
  obtain ⟨g,hgd,hgexp,hgim⟩ := exists_semidisk_logarithm hR hd (fun z hz => by
    exact norm_pos_iff.mp (hc.trans_le (hlower z hz)))
  have hM : 0≤ -Real.log c := neg_nonneg.mpr (Real.log_nonpos hc.le hc1)
  have hgp : ∀z∈upperSemidisk R,0<(g z).im := by
    intro z hz
    rw [hgim z hz]
    exact neg_pos.mpr (Real.log_neg (hc.trans_le (hlower z hz)) (hupper z hz))
  have hgb : ∀z∈upperSemidisk R,(g z).im≤ -Real.log c := by
    intro z hz
    rw [hgim z hz]
    exact neg_le_neg (Real.log_le_log hc (hlower z hz))
  have hgt : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => (g z).im) (𝓝[upperSemidisk R] p) (𝓝 0) := by
    intro p hp hp0
    have ht := ((Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp
      (htrace p hp hp0)).neg
    simp only [Real.log_one,neg_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hgim z hz).symm
  obtain ⟨G,hGc,hGeq⟩ := semidisk_continuous_extension hR hM hgd hgp hgb hgt
  let F : ℂ → ℂ := fun z => exp (I*G z)
  have hFc : Continuous F := continuous_exp.comp (continuous_const.mul hGc)
  have hFeq : EqOn F f (upperSemidisk (R/4)) := by
    intro z hz
    change exp (I*G z)=f z
    rw [hGeq hz]
    exact hgexp z (upperSemidisk_mono (by linarith : R/4≤R) hz)
  refine ⟨F,hFc,hFeq,?_⟩
  intro p hp hp0
  have hpcl : p∈closure (upperSemidisk (R/4)) := mem_closure_upperSemidisk hp hp0.ge
  have : NeBot (𝓝[upperSemidisk (R/4)] p) := mem_closure_iff_nhdsWithin_neBot.mp hpcl
  have ht := (htrace p (by linarith) hp0).mono_left
    (nhdsWithin_mono p (upperSemidisk_mono (by linarith : R/4≤R)))
  have hF : Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk (R/4)] p) (𝓝 ‖F p‖) := by
    apply (hFc.norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact congrArg norm (hFeq hz)
  exact tendsto_nhds_unique hF ht

end CircleDomainRigidity

end

end OAI
