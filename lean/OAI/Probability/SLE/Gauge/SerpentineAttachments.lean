import OAI.Probability.SLE.Gauge.SerpentineInfiniteArray

namespace OAI

/-! Clearance below the array and the unique attachment to its first
column. These facts separate the low connector from the array. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma array_normal_im_lower {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) :
    -(400 * (m : ℝ)) ≤ (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) z).im := by
  have hh : (0 : ℝ) < 100 * m := by positivity
  by_cases he : z.re ≤ arrayEnd m (2 * m)
  · rcases array_pieces m (2 * m) ⟨hz.1, he⟩ with ⟨i, hi, u, hu, _, hs, hT⟩ |
      ⟨i, hi, u, hu, _, hs, hT⟩
    · simp only [normalRibbon]
      rw [hs, hT, normal_straight_eq hm]
      have hb := columnPoint_bound hh hm hi 0 (straight_height_bound m i hu) hz.2
      rw [dist_zero_right] at hb
      have hi := Complex.abs_im_le_norm (columnPoint 0 (100 * m) m i (side i * (-100 * m + u)) z.im)
      have hl := neg_abs_le (columnPoint 0 (100 * m) m i (side i * (-100 * m + u)) z.im).im
      linarith
    · simp only [normalRibbon]
      rw [hs, hT, normal_circular_eq hm]
      have hb := turnPoint_bound hh hm (show i + 1 ≤ 2 * m by omega) 0 (u / 50) hz.2
      rw [dist_zero_right] at hb
      have hi := Complex.abs_im_le_norm (turnPoint 0 (100 * m) m i (u / 50) z.im)
      have hl := neg_abs_le (turnPoint 0 (100 * m) m i (u / 50) z.im).im
      linarith
  · have hE : columnEntry 0 m (2 * m) ≤ z.re := by
      have h := lt_of_not_ge he
      dsimp only [arrayEnd] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have ht := array_normal_terminal hm (a := z.im) hE
    rw [Complex.re_add_im z] at ht
    rw [ht, columnPoint_im]
    have h := lt_of_not_ge he
    dsimp only [arrayEnd] at h
    simp only [Complex.zero_im, zero_add]
    linarith

/-- The downward extension of the first column meets the array only at
its initial cross-section, with identical normal coordinate. -/
theorem array_downward_attachment {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) {y a : ℝ} (hy : y ≤ -(100 * (m : ℝ)))
    (ha : |a| ≤ 1)
    (he : normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) z =
      columnPoint 0 (100 * m) m 0 y a) :
    z.re = 0 ∧ y = -(100 * (m : ℝ)) ∧ z.im = a := by
  have hh : (0 : ℝ) < 100 * m := by positivity
  have hs0 : side 0 = 1 := by simp [side]
  by_cases hE : z.re ≤ arrayEnd m (2 * m)
  · rcases array_pieces m (2 * m) ⟨hz.1, hE⟩ with ⟨i, _, u, hu, hzu, hs, hT⟩ |
      ⟨i, hi, u, hu, _, hs, hT⟩
    · simp only [normalRibbon] at he
      rw [hs, hT, normal_straight_eq hm] at he
      have hii := columnPoint_equal_forces_index hh hm 0 _ _ hz.2 ha he
      subst i
      obtain ⟨hy', ha'⟩ := columnPoint_injective hh hm 0 0 he
      rw [hs0, one_mul] at hy'
      have hu0 : u = 0 := by linarith [hu.1]
      subst u
      exact ⟨by simpa [columnEntry] using hzu, by linarith, ha'⟩
    · simp only [normalRibbon] at he
      rw [hs, hT, normal_circular_eq hm] at he
      by_cases hi0 : i = 0
      · subst i
        have him := turn_oriented_height hh hm 0 0 (circular_angle_bound hu) hz.2
        rw [hs0, one_mul, he, columnPoint_im] at him
        simp only [Complex.zero_im, zero_add] at him
        linarith
      · exact (turnPoint_column_ne_nonadjacent hh hm (Or.inl (Nat.pos_of_ne_zero hi0))
          0 (u / 50) y hz.2 ha he).elim
  · have hze : columnEntry 0 m (2 * m) ≤ z.re := by
      have h := lt_of_not_ge hE
      dsimp only [arrayEnd] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have ht := array_normal_terminal hm (a := z.im) hze
    rw [Complex.re_add_im z] at ht
    rw [ht] at he
    have hii := columnPoint_equal_forces_index hh hm 0 _ _ hz.2 ha he
    omega

end SLEExactGauge.Serpentine

end

end OAI
