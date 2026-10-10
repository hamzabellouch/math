import OAI.Analysis.CircleDomains.Reflection.LocalModulusContinuation

namespace OAI

/-! Any continuous continuation agreeing on the upper side retains the
unit-circle boundary values forced by the interior modulus trace. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma norm_eq_one_on_real_continuation {R : ℝ} {V : Set ℂ} {f F : ℂ → ℂ}
    (hV : IsOpen V) (hVR : V⊆ball 0 R) (hF : ContinuousOn F V)
    (he : EqOn F f (V∩{z:ℂ | 0<z.im}))
    (ht : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 1))
    {p : ℂ} (hp : p∈V) (hp0 : p.im=0) : ‖F p‖=1 := by
  have hpn : ‖p‖<R := mem_ball_zero_iff.mp (hVR hp)
  have hpc : p∈closure (upperSemidisk R) := mem_closure_upperSemidisk hpn hp0.ge
  have : NeBot (𝓝[upperSemidisk R] p) := mem_closure_iff_nhdsWithin_neBot.mp hpc
  have heq : F =ᶠ[𝓝[upperSemidisk R] p] f := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hp),self_mem_nhdsWithin] with z hzV hzU
    exact he ⟨hzV,hzU.2⟩
  have hf : Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 ‖F p‖) := by
    apply ((hF.continuousAt (hV.mem_nhds hp)).norm.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact heq.mono (fun z hz => congrArg norm hz)
  exact tendsto_nhds_unique hf (ht p hpn.le hp0)

end CircleDomainRigidity

end

end OAI
