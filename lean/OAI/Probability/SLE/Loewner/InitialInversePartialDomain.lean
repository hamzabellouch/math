import OAI.Probability.SLE.Loewner.InitialLimitInverse
import OAI.Probability.SLE.Geometry.SubarcParameter

namespace OAI

/-! The inverse limit covers any fixed later subarc complement on which
the approximating charts are eventually defined. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma initialInverse_limit_covers_subarc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (b : unitInterval) (hb : b≠0)
    (hbt : ∀ᶠ n in atTop, t n≤b) :
    SurjOn F upperHalfPlane (upperHalfPlane \ range (initialSubarc p b)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbt
  let hib := initialSubarc_injective hi hb
  have h0b : initialSubarc p b 0=0 := by simpa only [initialSubarc_zero] using h0
  let hHb := initialSubarc_upper hH hb
  let u : ℕ → unitInterval := fun n => subarcParameter b hb (t (n+N))
  have he (n : ℕ) : b*u n=t (n+N) :=
    subarcParameter_mul_of_le b hb (hN (n+N) (by omega))
  have hshift := locallyUniform_reindex hlim (tendsto_add_atTop_nat N)
  have hq : TendstoLocallyUniformlyOn
      (fun n => initialInverseChart (initialSubarc p b) hib h0b hHb (u n)) F atTop upperHalfPlane := by
    apply hshift.congr
    intro n z hz
    have hh := initialInverseChart_subarc p hi h0 hH b hb hib h0b hHb (u n) hz
    rw [he n] at hh
    exact hh.symm
  exact initialInverse_limit_covers_final_domain (initialSubarc p b) hib h0b hHb hF hq

lemma exists_later_subarc_domain (p : C(unitInterval,ℂ)) (hi : Injective p)
    {s : unitInterval} (hs : s<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    ∃ b : unitInterval, s<b ∧ z∈upperHalfPlane \ range (initialSubarc p b) := by
  by_cases hzp : z∈range p
  · obtain ⟨u,hu⟩ := hzp
    have hsu : s<u := by
      by_contra hn
      apply hz.2
      rw [initialSubarc_range]
      exact ⟨u,⟨bot_le,le_of_not_gt hn⟩,hu⟩
    obtain ⟨b,hsb,hbu⟩ := exists_between hsu
    refine ⟨b,hsb,hz.1,?_⟩
    rw [initialSubarc_range]
    rintro ⟨v,hv,hv_eq⟩
    have hvu : v=u := hi (hv_eq.trans hu.symm)
    exact (not_le_of_gt hbu) (hvu ▸ hv.2)
  · refine ⟨1,hs,hz.1,?_⟩
    exact fun hh => hzp (initialSubarc_range_subset p 1 hh)

lemma initialInverse_limit_covers_at (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (ht : Tendsto t atTop (𝓝 s)) :
    SurjOn F upperHalfPlane (upperHalfPlane \ range (initialSubarc p s)) := by
  intro z hz
  by_cases hs : s=1
  · subst s
    apply initialInverse_limit_covers_final_domain p hi h0 hH hF hlim z
    simpa only [Set.mem_sdiff,mem_range,initialSubarc_apply,one_mul] using hz
  · obtain ⟨b,hsb,hzb⟩ := exists_later_subarc_domain p hi (lt_of_le_of_ne le_top hs) hz
    have hb : b≠0 := ne_of_gt (lt_of_le_of_lt bot_le hsb)
    exact initialInverse_limit_covers_subarc p hi h0 hH hF hlim b hb
      (ht.eventually (Iio_mem_nhds hsb) |>.mono fun _ hh => hh.le) hzb

end SLEExactGauge

end

end OAI
