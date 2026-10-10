import OAI.Analysis.CircleDomains.Selection.AtomlessQuantiles
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! A fixed countable family suffices for the four separated quantile arcs. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_rational_interval_inside (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) {r : ℝ≥0∞} (hr : r < μ (Ioo a b)) :
    ∃ l u : ℚ, a < (l : ℝ) ∧ l < u ∧ (u : ℝ) < b ∧ r < μ (Ioo (l : ℝ) (u : ℝ)) := by
  obtain ⟨K, hKsub, hK, hrK⟩ := measurableSet_Ioo.exists_lt_isCompact (μ := μ) hr
  have hKne : K.Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt (lt_of_le_of_lt bot_le hrK))
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne continuous_id.continuousOn
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hKne continuous_id.continuousOn
  obtain ⟨l, hal, hlx⟩ := exists_rat_btwn (hKsub hx).1
  obtain ⟨u, hyu, hub⟩ := exists_rat_btwn (hKsub hy).2
  have hlu : l < u := by exact_mod_cast (hlx.trans_le (hmax hx)).trans hyu
  refine ⟨l, u, hal, hlu, hub, hrK.trans_le (measure_mono ?_)⟩
  intro z hz
  exact ⟨hlx.trans_le (hmin hz), (hmax hz).trans_lt hyu⟩

theorem exists_four_ordered_rational_intervals (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ l u : Fin 4 → ℚ,
      (∀ i, l i < u i ∧ (1 / 10 : ℝ≥0∞) < μ (Ioo (l i : ℝ) (u i : ℝ))) ∧
      ∀ i j, i < j → u i < l j := by
  obtain ⟨q, hmono, hq⟩ := exists_eight_ordered_quantiles μ
  let L (i : Fin 4) : Fin 8 := ⟨2 * i.val, by omega⟩
  let U (i : Fin 4) : Fin 8 := ⟨2 * i.val + 1, by omega⟩
  have hm (i : Fin 4) : (1 / 10 : ℝ≥0∞) < μ (Ioo (q (L i)) (q (U i))) := by
    rw [atomless_measure_Ioo_cdf, hq, hq]
    have he : (((U i).val : ℝ) + 1) / 9 - (((L i).val : ℝ) + 1) / 9 = 1 / 9 := by
      simp only [L, U, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    rw [he]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  choose l u hl hlu hu hmass using fun i => exists_rational_interval_inside μ
    (q (L i)) (q (U i)) (hm i)
  refine ⟨l, u, fun i => ⟨hlu i, hmass i⟩, ?_⟩
  intro i j hij
  have hqij : q (U i) < q (L j) := hmono (by change 2 * i.val + 1 < 2 * j.val; omega)
  exact_mod_cast (hu i).trans (hqij.trans (hl j))

/-- If the law is supported between two cut points, the four intervals can be
chosen strictly inside those cut points. -/
theorem exists_four_ordered_rational_intervals_between (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (a b : ℝ)
    (ha : cdf μ a = 0) (hb : cdf μ b = 1) :
    ∃ l u : Fin 4 → ℚ,
      (∀ i, a < (l i : ℝ) ∧ l i < u i ∧ (u i : ℝ) < b ∧
        (1 / 10 : ℝ≥0∞) < μ (Ioo (l i : ℝ) (u i : ℝ))) ∧
      ∀ i j, i < j → u i < l j := by
  obtain ⟨q, hmono, hq⟩ := exists_eight_ordered_quantiles μ
  have hqa (i : Fin 8) : a < q i := by
    by_contra hn
    have h := (cdf μ).mono (le_of_not_gt hn)
    rw [ha, hq] at h
    have : (0 : ℝ) < ((i.val : ℝ) + 1) / 9 := by positivity
    linarith
  have hqb (i : Fin 8) : q i < b := by
    by_contra hn
    have h := (cdf μ).mono (le_of_not_gt hn)
    rw [hb, hq] at h
    have hi : (i.val : ℝ) < 8 := by exact_mod_cast i.isLt
    linarith
  let L (i : Fin 4) : Fin 8 := ⟨2 * i.val, by omega⟩
  let U (i : Fin 4) : Fin 8 := ⟨2 * i.val + 1, by omega⟩
  have hm (i : Fin 4) : (1 / 10 : ℝ≥0∞) < μ (Ioo (q (L i)) (q (U i))) := by
    rw [atomless_measure_Ioo_cdf, hq, hq]
    have he : (((U i).val : ℝ) + 1) / 9 - (((L i).val : ℝ) + 1) / 9 = 1 / 9 := by
      simp only [L, U, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  choose l u hl hlu hu hmass using fun i => exists_rational_interval_inside μ
    (q (L i)) (q (U i)) (hm i)
  refine ⟨l, u, fun i => ⟨(hqa _).trans (hl i), hlu i, (hu i).trans (hqb _), hmass i⟩, ?_⟩
  intro i j hij
  have hqij : q (U i) < q (L j) := hmono (by change 2 * i.val + 1 < 2 * j.val; omega)
  exact_mod_cast (hu i).trans (hqij.trans (hl j))

end CircleDomainRigidity

end

end OAI
