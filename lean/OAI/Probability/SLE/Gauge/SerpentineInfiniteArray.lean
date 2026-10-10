import OAI.Probability.SLE.Gauge.SerpentineArrayEmbedding
import OAI.Probability.SLE.Gauge.SerpentineTerminal

namespace OAI

/-! The finite serpentine remains embedded after continuing its last
column vertically to infinity. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma array_normal_terminal {m : ℕ} (hm : 0 < m) {t a : ℝ}
    (ht : columnEntry 0 m (2 * m) ≤ t) :
    normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) (t + a * Complex.I) =
      columnPoint 0 (100 * m) m (2 * m) (-100 * m + (t - columnEntry 0 m (2 * m))) a := by
  simp only [normalRibbon, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one, zero_add, add_zero]
  rw [arraySpine_tail m (2 * m) ht, arrayTangent_tail m (2 * m) ht, normal_straight_eq hm,
    side_even, one_mul]

lemma array_normal_finite_terminal_disjoint {m : ℕ} (hm : 0 < m) {z w : ℂ}
    (hz : z.re ∈ Icc (0 : ℝ) (arrayEnd m (2 * m)) ∧ |z.im| ≤ 1)
    (hw : arrayEnd m (2 * m) < w.re) (hwa : |w.im| ≤ 1) :
    normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) z ≠
      normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) w := by
  intro he
  have hh : (0 : ℝ) < 100 * m := by positivity
  have hwe : columnEntry 0 m (2 * m) ≤ w.re := by
    dsimp only [arrayEnd] at hw
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hwy : 100 * (m : ℝ) < -100 * m + (w.re - columnEntry 0 m (2 * m)) := by
    dsimp only [arrayEnd] at hw
    linarith
  have htw := array_normal_terminal hm (a := w.im) hwe
  rw [Complex.re_add_im w] at htw
  rw [htw] at he
  rcases array_pieces m (2 * m) hz.1 with ⟨i, _, u, hu, _, hs, hT⟩ |
    ⟨i, hi, u, hu, _, hs, hT⟩
  · simp only [normalRibbon] at he
    rw [hs, hT, normal_straight_eq hm] at he
    have hii := columnPoint_equal_forces_index hh hm 0 _ _ hz.2 hwa he
    subst i
    have hy := congrArg Complex.im he
    simp only [columnPoint_im, side_even, one_mul] at hy
    have hsmall := (abs_le.mp (straight_height_bound m (2 * m) hu)).2
    rw [side_even, one_mul] at hsmall
    linarith
  · simp only [normalRibbon] at he
    rw [hs, hT, normal_circular_eq hm] at he
    exact turnPoint_terminal_column_ne hh hm hi 0 (circular_angle_bound hu) hwy hz.2 hwa he

/-- The complete upward-continued array is embedded on the whole closed
width-one normal strip. -/
theorem array_normal_injective_infinite {m : ℕ} (hm : 0 < m) :
    InjOn (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)))
      {z : ℂ | 0 ≤ z.re ∧ |z.im| ≤ 1} := by
  intro z hz w hw he
  by_cases hzE : z.re ≤ arrayEnd m (2 * m)
  · by_cases hwE : w.re ≤ arrayEnd m (2 * m)
    · exact array_normal_injective hm (2 * m) ⟨⟨hz.1, hzE⟩, hz.2⟩ ⟨⟨hw.1, hwE⟩, hw.2⟩ he
    · exact (array_normal_finite_terminal_disjoint hm ⟨⟨hz.1, hzE⟩, hz.2⟩
        (lt_of_not_ge hwE) hw.2 he).elim
  · by_cases hwE : w.re ≤ arrayEnd m (2 * m)
    · exact (array_normal_finite_terminal_disjoint hm ⟨⟨hw.1, hwE⟩, hw.2⟩
        (lt_of_not_ge hzE) hz.2 he.symm).elim
    · have hze : columnEntry 0 m (2 * m) ≤ z.re := by
        have h := lt_of_not_ge hzE
        dsimp only [arrayEnd] at h
        linarith [Nat.cast_nonneg (α := ℝ) m]
      have hwe : columnEntry 0 m (2 * m) ≤ w.re := by
        have h := lt_of_not_ge hwE
        dsimp only [arrayEnd] at h
        linarith [Nat.cast_nonneg (α := ℝ) m]
      have htz := array_normal_terminal hm (a := z.im) hze
      have htw := array_normal_terminal hm (a := w.im) hwe
      rw [Complex.re_add_im z] at htz
      rw [Complex.re_add_im w] at htw
      rw [htz, htw] at he
      have hh : (0 : ℝ) < 100 * m := by positivity
      obtain ⟨hy, ha⟩ := columnPoint_injective hh hm 0 (2 * m) he
      exact Complex.ext (by linarith) ha

end SLEExactGauge.Serpentine

end

end OAI
