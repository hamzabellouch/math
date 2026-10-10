import OAI.Probability.SLE.Loewner.UnivalentInverseAnalytic

namespace OAI

/-! A nonconstant locally uniform limit of injective holomorphic maps is
injective. Boundary separation and the minimum principle provide the
local preimages needed for the proof. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma isolated_level_closedBall {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hnon : ¬∃ c, ∀ z∈D, f z=c) {a b : ℂ} (ha : a∈D) (hab : a≠b) :
    ∃ r>0, closedBall a r ⊆ D ∧ b∉closedBall a r ∧
      ∀ z∈sphere a r, f z≠f a := by
  have hn : ¬∀ᶠ z in 𝓝 a, f z=f a := by
    intro h
    exact hnon ⟨f a,fun z hz => (hf.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hconn ha h hz⟩
  have hne := ((hf.analyticAt (hD.mem_nhds ha)).eventually_eq_or_eventually_ne
    analyticAt_const).resolve_left hn
  have hh : ∀ᶠ z in 𝓝 a, z∈D ∧ z≠b ∧ (z≠a → f z≠f a) := by
    filter_upwards [hD.mem_nhds ha,isOpen_ne.mem_nhds hab,
      eventually_nhdsWithin_iff.mp hne] with z hz hzb hza
    exact ⟨hz,hzb,hza⟩
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hh
  refine ⟨r,hr,fun z hz => (hball hz).1,?_,?_⟩
  · intro hb
    exact (hball hb).2.1 rfl
  · intro z hz
    exact (hball (sphere_subset_closedBall hz)).2.2 (ne_of_mem_sphere hz hr.ne')

lemma tendstoLocallyUniformlyOn_injOn
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) D) (hi : ∀ n, InjOn (F n) D)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hnon : ¬∃ c, ∀ z∈D, f z=c) : InjOn f D := by
  have hf := hlim.differentiableOn (Eventually.of_forall hF) hD
  intro a ha b hb he
  by_contra hab
  obtain ⟨r,hr,hKD,hbK,hsep⟩ := isolated_level_closedBall hD hconn hf hnon ha hab
  have hc : ContinuousOn (fun z => ‖f z-f a‖) (sphere a r) :=
    ((hf.continuousOn.mono (sphere_subset_closedBall.trans hKD)).sub continuousOn_const).norm
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hc
  let δ : ℝ := ‖f w-f a‖
  have hδ : 0<δ := norm_pos_iff.mpr (sub_ne_zero.mpr (hsep w hw))
  have hlower (z : ℂ) (hz : z∈sphere a r) : δ≤‖f z-f a‖ := hmin hz
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp hlim
    (closedBall a r) hKD (isCompact_closedBall a r)
  have hε : 0<δ/8 := by positivity
  have hk := (Metric.tendstoUniformlyOn_iff.mp hu) (δ/8) hε
  have hbb := (Metric.tendsto_nhds.mp (hlim.tendsto_at hb)) (δ/8) hε
  obtain ⟨n,hkn,hbn⟩ := (hk.and hbb).exists
  have hnear (z : ℂ) (hz : z∈closedBall a r) : ‖F n z-f z‖<δ/8 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hkn z hz
  have hnearB : ‖F n b-f b‖<δ/8 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hbn
  have hnearA := hnear a (mem_closedBall_self hr.le)
  have hboundary (z : ℂ) (hz : z∈sphere a r) : δ/2≤‖F n z-F n a‖ := by
    have htri : ‖f z-f a‖ ≤ ‖f z-F n z‖+‖F n z-F n a‖+‖F n a-f a‖ := by
      calc
        _ = ‖(f z-F n z)+(F n z-F n a)+(F n a-f a)‖ := by congr 1; ring
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [norm_sub_rev (f z) (F n z)] at htri
    have hznear := hnear z (sphere_subset_closedBall hz)
    linarith [hlower z hz]
  have hsmall : F n b∈ball (F n a) ((δ/2)/2) := by
    rw [mem_ball,dist_eq_norm]
    have htri : ‖F n b-F n a‖≤‖F n b-f b‖+‖F n a-f a‖ := by
      rw [he]
      have h := norm_sub_le_norm_sub_add_norm_sub (F n b) (f b) (F n a)
      simpa only [norm_sub_rev (f b) (F n a)] using h
    linarith
  have hdc : DiffContOnCl ℂ (F n) (ball a r) :=
    ⟨(hF n).mono (ball_subset_closedBall.trans hKD),by
      rw [closure_ball a hr.ne']
      exact (hF n).continuousOn.mono hKD⟩
  have hnot : ∃ᶠ z in 𝓝 a, F n z≠F n a :=
    not_eventually.mp (univalent_not_eventually_constant hD (hi n) ha)
  obtain ⟨z,hz,heq⟩ := hdc.ball_subset_image_closedBall hr hboundary hnot hsmall
  have hzb : z=b := hi n (hKD hz) hb heq
  exact hbK (hzb ▸ hz)

end SLEExactGauge

end

end OAI
