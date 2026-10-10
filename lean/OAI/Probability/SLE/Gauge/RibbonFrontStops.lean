import OAI.Probability.SLE.Gauge.ProperRibbonCoordinates

namespace OAI

/-! One globally continuous ribbon progress coordinate supplies all
integer first-front stopping times. Their order is pathwise, including
infinite failure times, and successful histories identify them exactly. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage

lemma firstFrontTime_mono_of_initial
    (x : ℝ≥0 → ℝ) (hx : Continuous x) {a b : ℝ} (h0 : x 0 ≤ a) (hab : a ≤ b) :
    firstFrontTime x a ≤ firstFrontTime x b := by
  by_cases hb : ∃ t : ℝ≥0, 0 ≤ t ∧ x t - b ∈ ({0} : Set ℝ)
  · have ha : ∃ t : ℝ≥0, 0 ≤ t ∧ x t - a ∈ ({0} : Set ℝ) := by
      obtain ⟨t, ht, htb⟩ := hb
      have he : x t = b := sub_eq_zero.mp htb
      obtain ⟨u, _, hue⟩ := intermediate_value_Icc ht hx.continuousOn
        ⟨h0, by rw [he]; exact hab⟩
      exact ⟨u, bot_le, by simp only [hue, sub_self, mem_singleton_iff]⟩
    unfold firstFrontTime hittingAfter
    rw [ite_eq_left ha, ite_eq_left hb, WithTop.coe_le_coe]
    apply le_csInf hb
    intro t ht
    have he : x t = b := sub_eq_zero.mp ht.2
    obtain ⟨u, hu, hue⟩ := intermediate_value_Icc ht.1 hx.continuousOn
      ⟨h0, by rw [he]; exact hab⟩
    have hle : sInf {t : ℝ≥0 | 0 ≤ t ∧ x t - a ∈ ({0} : Set ℝ)} ≤ u :=
      csInf_le (OrderBot.bddBelow _) ⟨bot_le, by simp only [hue, sub_self, mem_singleton_iff]⟩
    exact hle.trans hu.2
  · have he : firstFrontTime x b = ⊤ := by
      unfold firstFrontTime hittingAfter
      rw [ite_eq_right hb]
    rw [he]
    exact le_top

def ribbonFrontStop {Ω : Type*} (g : C(ℂ, ℝ)) (γ : Ω → ℝ≥0 → ℂ)
    (k : ℝ) (ω : Ω) : WithTop ℝ≥0 := firstFrontTime (fun t => g (γ ω t)) k

lemma ribbonFrontStop_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (g : C(ℂ, ℝ)) (γ : Ω → ℝ≥0 → ℂ)
    (ha : Adapted ℱ (fun t ω => γ ω t)) (hc : ∀ ω, Continuous (γ ω)) (k : ℝ) :
    IsStoppingTime ℱ (ribbonFrontStop g γ k) :=
  firstFrontTime_isStoppingTime ℱ (fun t ω => g (γ ω t))
    (fun t => g.continuous.measurable.comp (ha t)) (fun ω => g.continuous.comp (hc ω)) k

lemma ribbonFrontStop_monotone
    {Ω : Type*} (g : C(ℂ, ℝ)) (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (h0 : ∀ ω, g (γ ω 0) = 0) :
    ∀ ω, Monotone (fun n : ℕ => ribbonFrontStop g γ (n : ℝ) ω) := by
  intro ω n k hnk
  exact firstFrontTime_mono_of_initial _ (g.continuous.comp (hc ω))
    (by change g (γ ω 0) ≤ (n : ℝ); rw [h0 ω]; positivity) (by exact_mod_cast hnk)

/-- The global first front agrees with the actual time in a successful
history, irrespective of the extension away from the physical ribbon. -/
lemma RibbonHistory.global_frontStop_eq
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) (g : C(ℂ, ℝ))
    (hg : ∀ z ∈ closedRibbon, g (d.chart z) = z.re) :
    firstFrontTime (fun t => g (d.trace t)) d.front = (d.time : WithTop ℝ≥0) := by
  have heq (t : ℝ≥0) (ht : t ∈ Icc 0 d.time) :
      g (d.trace t) = (d.coordinates t).re := by
    rw [d.trace_coordinates ht]
    exact hg _ (d.coordinates_ribbon ht)
  have hattain : g (d.trace d.time) = d.front := by
    rw [heq _ ⟨bot_le, le_rfl⟩, d.attained]
    simp
  have hleast : IsLeast {t : ℝ≥0 | 0 ≤ t ∧ g (d.trace t) - d.front ∈ ({0} : Set ℝ)}
      d.time := by
    refine ⟨⟨bot_le, by simp only [hattain, sub_self, mem_singleton_iff]⟩, ?_⟩
    intro t ht
    by_contra hn
    have hlt : t < d.time := lt_of_not_ge hn
    have hh := d.strict_past t hlt
    rw [← heq t ⟨bot_le, hlt.le⟩, sub_eq_zero.mp ht.2] at hh
    exact (lt_irrefl _ hh)
  unfold firstFrontTime hittingAfter
  rw [ite_eq_left ⟨d.time, hleast.1⟩, hleast.csInf_eq]

end SLEExactGauge

end

end OAI
