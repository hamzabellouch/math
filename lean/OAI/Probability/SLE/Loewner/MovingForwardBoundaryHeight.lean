import OAI.Probability.SLE.Loewner.InitialInverseJointContinuity
import OAI.Probability.SLE.Loewner.SlitUniformForwardBound
import OAI.Probability.SLE.Loewner.FutureSlitDomain

namespace OAI

/-! Bounded moving forward coordinates can only approach the real line
when their physical point reaches the limiting slit boundary. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma initialForward_uniform_near (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s))
    (hzR : ‖z‖≤2*R) :
    ‖initialForwardChart p hi h0 hH s z‖≤(512*Real.pi+9)*R := by
  by_cases hs : s=0
  · subst s
    rw [initialForwardChart_zero]
    change ‖z‖≤_
    nlinarith [Real.pi_pos]
  · rw [initialForwardChart,dite_eq_right hs]
    exact (initialSlitChart p hi h0 hH s hs).forward_uniform_near
      (initialSubarc_injective hi hs) (by simpa only [initialSubarc_zero] using h0)
      (initialSubarc_upper hH hs) hR (fun u => hp _) hz hzR

theorem initialForward_boundary_height_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {t : ℕ → unitInterval} {s : unitInterval} {z : ℕ → ℂ} {b : ℂ}
    (ht : Tendsto t atTop (𝓝 s)) (hz : Tendsto z atTop (𝓝 b))
    (hzd : ∀ n, z n∈upperHalfPlane \ range (initialSubarc p (t n)))
    (hb : b∉upperHalfPlane \ range (initialSubarc p s))
    {M : ℝ} (hM : ∀ n, ‖initialForwardChart p hi h0 hH (t n) (z n)‖≤M) :
    Tendsto (fun n => (initialForwardChart p hi h0 hH (t n) (z n)).im) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨w,_,ψ,hψ,hw⟩ := (isCompact_closedBall (0:ℂ) M).tendsto_subseq (fun n => by
    rw [mem_closedBall_zero_iff]
    exact hM (φ n))
  have hwim : 0≤w.im := ge_of_tendsto (continuous_im.continuousAt.tendsto.comp hw)
    (Eventually.of_forall fun n =>
      (show 0<(initialForwardChart p hi h0 hH (t (φ (ψ n))) (z (φ (ψ n)))).im from
        initialForwardChart_mem_upper p hi h0 hH _ (hzd _)).le)
  have hwzero : w.im=0 := by
    by_contra hne
    have hwH : w∈upperHalfPlane := lt_of_le_of_ne hwim (Ne.symm hne)
    have htu := (ht.comp hφ).comp hψ.tendsto_atTop
    have hwu : Tendsto (fun n => (⟨initialForwardChart p hi h0 hH (t (φ (ψ n)))
        (z (φ (ψ n))),initialForwardChart_mem_upper p hi h0 hH _ (hzd _)⟩ : upperHalfPlane))
        atTop (𝓝 (⟨w,hwH⟩ : upperHalfPlane)) := by
      apply tendsto_subtype_rng.mpr
      exact hw
    have hback := ((initialInverseChart_joint_continuous p hi h0 hH).tendsto
      (s,(⟨w,hwH⟩ : upperHalfPlane))).comp (htu.prodMk_nhds hwu)
    have he : initialInverseChart p hi h0 hH s w=b := by
      apply tendsto_nhds_unique hback
      have hzu := (hz.comp hφ).comp hψ.tendsto_atTop
      apply hzu.congr
      intro n
      exact (initialInverse_forward_at p hi h0 hH _ (hzd _)).symm
    exact hb (he ▸ initialInverseChart_mem_domain p hi h0 hH s hwH)
  refine ⟨ψ,?_⟩
  have hh := continuous_im.continuousAt.tendsto.comp hw
  change Tendsto (fun n => (initialForwardChart p hi h0 hH (t (φ (ψ n)))
    (z (φ (ψ n)))).im) atTop (𝓝 w.im) at hh
  rwa [hwzero] at hh

end SLEExactGauge

end

end OAI
