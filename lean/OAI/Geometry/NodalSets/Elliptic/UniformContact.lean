import Mathlib.Analysis.Normed.Group.Bounded
import OAI.Geometry.NodalSets.Charts.NormalFrameContinuous
import OAI.Geometry.NodalSets.Waves.WaveEstimates

namespace OAI

namespace Yau.Jets
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma compact_positive_bounds {s : Set T} (hs : IsCompact s) (f : T → ℝ)
    (hf : ContinuousOn f s) (hpos : ∀ t ∈ s, 0 < f t) :
    ∃ c > 0, ∃ C > 0, ∀ t ∈ s, c ≤ f t ∧ f t ≤ C := by
  by_cases hn : s.Nonempty
  · obtain ⟨u, hu, hmin⟩ := hs.exists_isMinOn hn hf
    obtain ⟨v, hv, hmax⟩ := hs.exists_isMaxOn hn hf
    exact ⟨f u, hpos u hu, f v, hpos v hv, fun t ht ↦ ⟨hmin ht, hmax ht⟩⟩
  · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro t ht
    exact (hn ⟨t, ht⟩).elim

theorem normal_frame_eta_uniform {s : Set T} (hs : IsCompact s)
    (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (hH : ∀ i j, Continuous (fun t ↦ H t i j)) (ha0 : ∀ t, a t ≠ 0)
    (hstrict : ∀ t ∈ s, 0 < a t ^ 2 * H t 0 0 + b t ^ 2 * H t 1 1) :
    ∃ c > 0, ∃ C > 0, ∀ t ∈ s,
      c ≤ Yau.contactEta (a t) (b t) (H t 0 0) (H t 1 1) ∧
      Yau.contactEta (a t) (b t) (H t 0 0) (H t 1 1) ≤ C :=
  compact_positive_bounds hs _ (contactEta_continuous a b H ha hb hH ha0).continuousOn
    (fun t ht ↦ Yau.contactEta_pos (ha0 t) (hstrict t ht))

theorem uniform_cubic_remainder {s : Set T} (hs : IsCompact s)
    (f : T → Coord → ℝ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hc : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ 3 (f z.1) z.2))
    (hz : ∀ t ∈ s, ∀ k, k ≤ 2 → iteratedFDeriv ℝ k (f t) 0 = 0) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ 1 → |f t x| ≤ C * ‖x‖ ^ 3 := by
  obtain ⟨C, hC, hb⟩ := ((hs.prod (isCompact_closedBall (0:Coord) 1)).image hc).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  have hseg : ∀ r ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 3 (f t) (0 + r • x)‖ ≤ C := by
    intro r hr
    apply hb _
    refine ⟨(t,r • x), ⟨ht, ?_⟩, by simp⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg x)).trans (by simpa using hx)
  have hbnd := Yau.Waves.vanishing_jet_taylor_bound (n := 2)
    ((hf t).of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
    (0:Coord) x C (hz t ht) hseg
  simp only [zero_add, Real.norm_eq_abs] at hbnd
  norm_num at hbnd
  exact hbnd.trans (by nlinarith [mul_nonneg hC.le (pow_nonneg (norm_nonneg x) 3)])

theorem uniform_negative_contact {s : Set T} (hs : IsCompact s)
    (eta : T → ℝ) (heta : ContinuousOn eta s) (hpos : ∀ t ∈ s, 0 < eta t)
    (gap remainder : T → Coord → ℝ)
    (hf : ∀ t, ContDiff ℝ ∞ (remainder t))
    (hc : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ 3 (remainder z.1) z.2))
    (hz : ∀ t ∈ s, ∀ k, k ≤ 2 → iteratedFDeriv ℝ k (remainder t) 0 = 0)
    (hgap : ∀ t ∈ s, ∀ x, gap t x ≤ -(eta t / 2) * ‖x‖^2 + remainder t x) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) → gap t x ≤ -c*‖x‖^2 := by
  obtain ⟨e, he, _, _, heB⟩ := compact_positive_bounds hs eta heta hpos
  obtain ⟨C, hC, hb⟩ := uniform_cubic_remainder hs remainder hf hc hz
  have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div, mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
  have hsmall := ht.eventually (eventually_lt_nhds (lt_min (by norm_num : (0:ℝ) < 1)
    (div_pos he (mul_pos (by norm_num : (0:ℝ)<4) hC))))
  refine ⟨e/4, by positivity, ?_⟩
  filter_upwards [hsmall] with N hN
  intro t hts x hx
  have hx1 : ‖x‖ ≤ 1 := hx.trans (le_of_lt (lt_of_lt_of_le hN (min_le_left _ _)))
  have hxC : C * ‖x‖ ≤ e / 4 := by
    have hh := hx.trans (le_of_lt (lt_of_lt_of_le hN (min_le_right _ _)))
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hC)).mp hh
    nlinarith
  have hr := (le_abs_self (remainder t x)).trans (hb t hts x hx1)
  have hq : gap t x ≤ -(e/2)*‖x‖^2 + C*‖x‖^3 := by
    have he' := mul_le_mul_of_nonneg_right (heB t hts).1 (sq_nonneg ‖x‖)
    have hg := hgap t hts x
    nlinarith
  exact Yau.Waves.quadratic_gap_of_cubic_remainder (norm_nonneg x) hxC hq

end
end Yau.Jets

end OAI
