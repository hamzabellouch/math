import OAI.Probability.FKPressure.ComplexSeries

namespace OAI

 

noncomputable section
open Finset Set
open scoped Classical Topology
namespace BelowOne.PressureSeries
variable {V : Type*} [Fintype V]

lemma identity_on_disk_of_real_cube {f g : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 r))
    (he : ∀ t : ℝ, t ∈ Set.Icc 0 1 → f (t : ℂ) = g (t : ℂ)) :
    EqOn f g (Metric.ball 0 r) := by
  apply hf.eqOn_of_preconnected_of_mem_closure hg (convex_ball (0 : ℂ) r).isPreconnected
    (show (0 : ℂ) ∈ Metric.ball 0 r by simpa using zero_lt_one.trans hr)
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t : ℝ := min ε 1 / 2
  have ht : 0 < t := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have ht1 : t ≤ 1 := by dsimp [t]; linarith [min_le_right ε 1]
  have htε : t < ε := by dsimp [t]; linarith [min_le_left ε 1]
  refine ⟨(t : ℂ), ⟨he t ⟨ht.le,ht1⟩, ?_⟩, ?_⟩
  · simpa only [mem_singleton_iff, Complex.ofReal_eq_zero] using ne_of_gt ht
  · simpa only [dist_zero_left, Complex.norm_real, Real.norm_of_nonneg ht.le] using htε

lemma identity_on_polydisk {f g : (V → ℂ) → ℂ} {r : ℝ} (hr : 1 < r)
    (hf : AnalyticOnNhd ℂ f {x | ∀ i, ‖x i‖ < r})
    (hg : AnalyticOnNhd ℂ g {x | ∀ i, ‖x i‖ < r})
    (he : ∀ t : V → ℝ, (∀ i, t i ∈ Set.Icc 0 1) →
      f (fun i => (t i : ℂ)) = g (fun i => (t i : ℂ))) :
    EqOn f g {x | ∀ i, ‖x i‖ < r} := by
  have hfinite : ∀ s : Finset V, ∀ x : V → ℂ,
      (∀ i, ‖x i‖ < r) → (∀ i ∉ s, ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ x i = (t : ℂ)) →
        f x = g x := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro x hx hreal
      have hreal' : ∀ i, ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ x i = (t : ℂ) :=
        fun i => hreal i (by simp)
      choose t ht htx using hreal'
      have hh : x = fun i => (t i : ℂ) := funext htx
      rw [hh]
      exact he t ht
    | @insert i s his ih =>
      intro x hx hreal
      let curve : ℂ → V → ℂ := fun z => Function.update x i z
      have hc (z : ℂ) : AnalyticAt ℂ curve z := by
        apply AnalyticAt.pi
        intro j
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
          exact analyticAt_id
        · simpa only [curve, Function.update_of_ne hji] using
            (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => x j) z)
      have hb {z : ℂ} (hz : z ∈ Metric.ball 0 r) : ∀ j, ‖curve z j‖ < r := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [curve, Function.update_self, Metric.mem_ball, dist_zero_right] using hz
        · simpa only [curve, Function.update_of_ne hji] using hx j
      have hfc : AnalyticOnNhd ℂ (fun z => f (curve z)) (Metric.ball 0 r) :=
        fun z hz => (hf (curve z) (hb hz)).comp (hc z)
      have hgc : AnalyticOnNhd ℂ (fun z => g (curve z)) (Metric.ball 0 r) :=
        fun z hz => (hg (curve z) (hb hz)).comp (hc z)
      have hec : ∀ t : ℝ, t ∈ Set.Icc 0 1 → f (curve (t : ℂ)) = g (curve (t : ℂ)) := by
        intro t ht
        apply ih (curve (t : ℂ))
        · apply hb
          simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht.1] using ht.2.trans_lt hr
        · intro j hjs
          by_cases hji : j = i
          · subst j
            exact ⟨t,ht,Function.update_self _ _ _⟩
          · obtain ⟨u,hu,hxu⟩ := hreal j (by simp only [Finset.mem_insert]; exact not_or.mpr ⟨hji,hjs⟩)
            exact ⟨u,hu, by simpa only [curve, Function.update_of_ne hji] using hxu⟩
      have hres := identity_on_disk_of_real_cube hr hfc hgc hec
      simpa only [curve, Function.update_eq_self] using
        hres (show x i ∈ Metric.ball 0 r by simpa only [Metric.mem_ball, dist_zero_right] using hx i)
  intro x hx
  exact hfinite univ x hx (fun i hi => False.elim (hi (mem_univ i)))

end BelowOne.PressureSeries

end

end OAI
