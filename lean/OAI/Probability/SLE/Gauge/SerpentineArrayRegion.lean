import OAI.Probability.SLE.Gauge.SerpentineAttachments

namespace OAI

/-! Horizontal confinement of the whole infinite array. This keeps
every part of the completed experiment away from the marked-point shadow. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma array_normal_re_lower {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) :
    -(400 * (m : ℝ)) ≤ (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) z).re := by
  have hh : (0 : ℝ) < 100 * m := by positivity
  by_cases he : z.re ≤ arrayEnd m (2 * m)
  · rcases array_pieces m (2 * m) ⟨hz.1, he⟩ with ⟨i, hi, u, hu, _, hs, hT⟩ |
      ⟨i, hi, u, hu, _, hs, hT⟩
    · simp only [normalRibbon]
      rw [hs, hT, normal_straight_eq hm]
      have hb := columnPoint_bound hh hm hi 0 (straight_height_bound m i hu) hz.2
      rw [dist_zero_right] at hb
      have hi := Complex.abs_re_le_norm (columnPoint 0 (100 * m) m i (side i * (-100 * m + u)) z.im)
      have hl := neg_abs_le (columnPoint 0 (100 * m) m i (side i * (-100 * m + u)) z.im).re
      linarith
    · simp only [normalRibbon]
      rw [hs, hT, normal_circular_eq hm]
      have hb := turnPoint_bound hh hm (show i + 1 ≤ 2 * m by omega) 0 (u / 50) hz.2
      rw [dist_zero_right] at hb
      have hi := Complex.abs_re_le_norm (turnPoint 0 (100 * m) m i (u / 50) z.im)
      have hl := neg_abs_le (turnPoint 0 (100 * m) m i (u / 50) z.im).re
      linarith
  · have hE : columnEntry 0 m (2 * m) ≤ z.re := by
      have h := lt_of_not_ge he
      dsimp only [arrayEnd] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have ht := array_normal_terminal hm (a := z.im) hE
    rw [Complex.re_add_im z] at ht
    rw [ht, columnPoint_re]
    simp only [columnOffset, normalized_spacing hm, normalized_width hm, side_even,
      one_mul, Complex.zero_re, zero_add, Nat.cast_mul, Nat.cast_ofNat]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [(abs_le.mp hz.2).2]

end SLEExactGauge.Serpentine

end

end OAI
