import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered

namespace OAI

noncomputable section

namespace InternalCatalan.GlobalMaxReduction

open Set Filter
open scoped Topology

theorem le_on_Icc_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (ha : f a ≤ M) (hb : f b ≤ M)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Icc a b, f x ≤ M := by
  intro x hx
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hcont
  have hcM : f c ≤ M := by
    by_cases hca : c = a
    · simpa only [hca] using ha
    by_cases hcb : c = b
    · simpa only [hcb] using hb
    have hcint : c ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hc.1 (Ne.symm hca), lt_of_le_of_ne hc.2 hcb⟩
    have hlocal : IsLocalMax f c :=
      hmax.isLocalMax (Icc_mem_nhds hcint.1 hcint.2)
    exact hcritical c hcint hlocal.deriv_eq_zero
  exact (hmax hx).trans hcM

theorem exists_left_cutoff {f : ℝ → ℝ} {a x M : ℝ}
    (hlim : Tendsto f (𝓝[>] a) atBot) (hax : a < x) :
    ∃ l ∈ Ioo a x, f l ≤ M := by
  have hinterval : ∀ᶠ l in 𝓝[>] a, l ∈ Ioo a x := Ioo_mem_nhdsGT hax
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem exists_right_cutoff {f : ℝ → ℝ} {x b M : ℝ}
    (hlim : Tendsto f (𝓝[<] b) atBot) (hxb : x < b) :
    ∃ r ∈ Ioo x b, f r ≤ M := by
  have hinterval : ∀ᶠ r in 𝓝[<] b, r ∈ Ioo x b := Ioo_mem_nhdsLT hxb
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem le_on_Ioo_of_limits_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  intro x hx
  obtain ⟨l, hl, hlM⟩ := exists_left_cutoff (M := M) hleft hx.1
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hl.1 hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) hlM hrM
    (fun c hc hd => hcritical c (hsub ⟨hc.1.le, hc.2.le⟩) hd)
    x ⟨hl.2.le, hr.1.le⟩

theorem le_on_Ico_of_limit_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ico a b))
    (ha : f a ≤ M)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ico a b, f x ≤ M := by
  intro x hx
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc a r ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) ha hrM
    (fun c hc hd => hcritical c ⟨hc.1, hc.2.trans hr.2⟩ hd)
    x ⟨hx.1, hr.1.le⟩

theorem le_on_Ioo_of_stationary_cover {f : ℝ → ℝ} {a b M : ℝ} {S : Set ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcover : ∀ c ∈ Ioo a b, deriv f c = 0 → c ∈ S)
    (hvalues : ∀ c ∈ S, f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  exact le_on_Ioo_of_limits_of_critical_le hcont hleft hright
    (fun c hc hd => hvalues c (hcover c hc hd))

theorem le_on_two_components_of_stationary_cover
    {f : ℝ → ℝ} {a c b M : ℝ} {S : Set ℝ}
    (hcontLeft : ContinuousOn f (Ico a c))
    (hcontRight : ContinuousOn f (Ioo c b))
    (ha : f a ≤ M)
    (hcLeft : Tendsto f (𝓝[<] c) atBot)
    (hcRight : Tendsto f (𝓝[>] c) atBot)
    (hbLeft : Tendsto f (𝓝[<] b) atBot)
    (hcover : ∀ x ∈ Ioo a c ∪ Ioo c b, deriv f x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, f x ≤ M) :
    ∀ x ∈ Ico a c ∪ Ioo c b, f x ≤ M := by
  intro x hx
  rcases hx with hx | hx
  · exact le_on_Ico_of_limit_of_critical_le hcontLeft ha hcLeft
      (fun z hz hd => hvalues z (hcover z (Or.inl hz) hd)) x hx
  · exact le_on_Ioo_of_limits_of_critical_le hcontRight hcRight hbLeft
      (fun z hz hd => hvalues z (hcover z (Or.inr hz) hd)) x hx

end InternalCatalan.GlobalMaxReduction

end

end OAI
