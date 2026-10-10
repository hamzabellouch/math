import Mathlib
import OAI.Analysis.Crouzeix.Montel

namespace OAI

/-! Hurwitz. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem zero_or_ne_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f l U)
    (hd : ∀ i, DifferentiableOn ℂ (F i) U)
    (hz : ∀ i z, z ∈ U → F i z ≠ 0) :
    EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  classical
  by_cases heq : EqOn f 0 U
  · exact Or.inl heq
  refine Or.inr (fun a ha hfa => ?_)
  have han := (hlim.differentiableOn (Eventually.of_forall hd) hU).analyticOnNhd hU
  rcases (han a ha).eventually_eq_zero_or_eventually_ne_zero with he | hn
  · exact heq (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc ha he)
  have hh : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (z ≠ a → f z ≠ 0) := by
    filter_upwards [hU.mem_nhds ha, eventually_nhdsWithin_iff.mp hn] with z hz1 hz2
    exact ⟨hz1, hz2⟩
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hh
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  have hsU : closedBall a r ⊆ U := fun z hz =>
    (hRsub (closedBall_subset_ball hrR hz)).1
  have hsz : ∀ z ∈ sphere a r, f z ≠ 0 := by
    intro z hz1
    apply (hRsub (closedBall_subset_ball hrR (sphere_subset_closedBall hz1))).2
    intro he
    subst z
    have hh : (0 : ℝ) = r := by simpa using hz1
    exact hr.ne' hh.symm
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (han.continuousOn.norm.mono (sphere_subset_closedBall.trans hsU))
  let δ := ‖f b‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hsz b hb)
  have hconv : TendstoUniformlyOn F f l (sphere a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim (sphere a r)
      (sphere_subset_closedBall.trans hsU) (isCompact_sphere a r)
  have hbound : ∀ᶠ i in l, δ / 2 ≤ ‖F i a‖ := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (by positivity)] with i hi
    have hlow : ∀ z ∈ sphere a r, δ / 2 ≤ ‖F i z‖ := by
      intro z hz1
      have hmi : δ ≤ ‖f z‖ := hmin hz1
      have herr : ‖f z - F i z‖ < δ / 2 := by simpa [dist_eq_norm] using hi z hz1
      have := norm_sub_norm_le (f z) (F i z)
      linarith
    have hi' : ‖(F i a)⁻¹‖ ≤ (δ / 2)⁻¹ := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le
        (f := fun z => (F i z)⁻¹) (z := a) (isBounded_ball (x := a) (r := r)) ?_ ?_ ?_
      · apply DifferentiableOn.diffContOnCl
        rw [closure_ball a hr.ne']
        apply DifferentiableOn.inv
        · exact (hd i).mono hsU
        · exact fun z hz1 => hz i z (hsU hz1)
      · intro z hz1
        rw [frontier_ball a hr.ne'] at hz1
        rw [norm_inv]
        exact inv_anti₀ (by positivity) (hlow z hz1)
      · exact subset_closure (mem_ball_self hr)
    rw [norm_inv] at hi'
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hz i a ha)) (by positivity)).mp hi'
  have hle := ge_of_tendsto (hlim.tendsto_at ha).norm hbound
  rw [hfa, norm_zero] at hle
  linarith

theorem injOn_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f l U)
    (hd : ∀ i, DifferentiableOn ℂ (F i) U) (hi : ∀ i, InjOn (F i) U)
    (hnc : ¬ ∃ c, EqOn f (fun _ => c) U) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hnb : a ∈ U ∩ {b}ᶜ := ⟨ha, hne⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hU.inter isClosed_singleton.isOpen_compl) a hnb
  have hsubU : ball a r ⊆ U := fun _ hz => (hsub hz).1
  have hl : TendstoLocallyUniformlyOn (fun i z => F i z - F i b)
      (fun z => f z - f b) l (ball a r) := by
    have hconst := ((hlim.tendsto_at hb).tendstoUniformlyOn_const (s := ball a r)).tendstoLocallyUniformlyOn
    exact (uniformContinuous_fst.sub uniformContinuous_snd).comp_tendstoLocallyUniformlyOn
      ((hlim.mono hsubU).prodMk hconst)
  have hdz : ∀ i, DifferentiableOn ℂ (fun z => F i z - F i b) (ball a r) :=
    fun i => ((hd i).mono hsubU).sub_const _
  have hzero : ∀ i z, z ∈ ball a r → F i z - F i b ≠ 0 := by
    intro i z hz he
    exact (hsub hz).2 (hi i (hsubU hz) hb (sub_eq_zero.mp he))
  rcases zero_or_ne_of_tendstoLocallyUniformlyOn isOpen_ball (convex_ball a r).isPreconnected
      hl hdz hzero with he | hn
  · apply hnc
    refine ⟨f b, ?_⟩
    apply (hlim.differentiableOn (Eventually.of_forall hd) hU).analyticOnNhd hU
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc ha
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact sub_eq_zero.mp (he hz)
  · exact hn a (mem_ball_self hr) (sub_eq_zero.mpr hab)

end CrouzeixHilbert.Conformal

end

end OAI
