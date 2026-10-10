import OAI.Probability.SLE.Gauge.SerpentineCurve
import OAI.Probability.SLE.Gauge.SerpentineEmbedding

namespace OAI

/-! Global normal coordinates for the actual finite serpentine array.
Every parameter belongs to a straight or circular piece, and the only
possible normal-band contacts are the prescribed common end sections. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

def arrayEnd (m j : ℕ) : ℝ := columnEntry 0 m j + 200 * m

lemma array_pieces (m j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (arrayEnd m j)) :
    (∃ i ≤ j, ∃ u ∈ Icc (0 : ℝ) (200 * m),
      t = columnEntry 0 m i + u ∧
      arraySpine m j t = straightPiece m i u ∧ arrayTangent m j t = straightTangent i) ∨
    (∃ i < j, ∃ u ∈ Icc (0 : ℝ) (50 * Real.pi),
      t = columnEntry 0 m i + 200 * m + u ∧
      arraySpine m j t = circularPiece m i u ∧ arrayTangent m j t = circularTangent i u) := by
  induction j with
  | zero =>
    exact Or.inl ⟨0, le_rfl, t, ⟨ht.1, by simpa only [arrayEnd, columnEntry, Nat.cast_zero, zero_mul, add_zero, zero_add] using ht.2⟩,
      by simp [columnEntry], rfl, rfl⟩
  | succ j ih =>
    have ha : arrayEnd m j < columnEntry 0 m (j + 1) := by
      rw [arrayEnd, columnEntry_succ]
      linarith [Real.pi_pos]
    by_cases hta : t ≤ arrayEnd m j
    · change t ≤ columnEntry 0 m j + 200 * m at hta
      rcases ih ⟨ht.1, hta⟩ with ⟨i, hi, u, hu, htu, hs, hT⟩ | ⟨i, hi, u, hu, htu, hs, hT⟩
      · refine Or.inl ⟨i, hi.trans (Nat.le_succ j), u, hu, htu, ?_, ?_⟩
        · simpa only [arraySpine, curveJoin_of_le (hta.trans ha.le), curveJoin_of_le hta] using hs
        · simpa only [arrayTangent, curveJoin_of_le (hta.trans ha.le), curveJoin_of_le hta] using hT
      · refine Or.inr ⟨i, hi.trans_le (Nat.le_succ j), u, hu, htu, ?_, ?_⟩
        · simpa only [arraySpine, curveJoin_of_le (hta.trans ha.le), curveJoin_of_le hta] using hs
        · simpa only [arrayTangent, curveJoin_of_le (hta.trans ha.le), curveJoin_of_le hta] using hT
    · have hat : columnEntry 0 m j + 200 * m < t := lt_of_not_ge hta
      by_cases htb : t ≤ columnEntry 0 m (j + 1)
      · refine Or.inr ⟨j, Nat.lt_succ_self j, t - arrayEnd m j, ?_, ?_, ?_, ?_⟩
        · constructor
          · linarith
          · rw [columnEntry_succ] at htb
            dsimp [arrayEnd]
            linarith
        · dsimp [arrayEnd]; ring
        · simp only [arraySpine, curveJoin_of_le htb, curveJoin_of_gt hat, arrayEnd]
        · simp only [arrayTangent, curveJoin_of_le htb, curveJoin_of_gt hat, arrayEnd]
      · have hbt : columnEntry 0 m (j + 1) < t := lt_of_not_ge htb
        refine Or.inl ⟨j + 1, le_rfl, t - columnEntry 0 m (j + 1), ?_, by ring, ?_, ?_⟩
        · constructor
          · linarith
          · dsimp only [arrayEnd] at ht
            linarith [ht.2]
        · exact arraySpine_tail m (j + 1) hbt.le
        · exact arrayTangent_tail m (j + 1) hbt.le

lemma normalized_width {m : ℕ} (hm : 0 < m) : ribbonWidth (100 * m) m = 1 := by
  unfold ribbonWidth
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma normalized_spacing {m : ℕ} (hm : 0 < m) : spacing (100 * m) m = 100 := by
  rw [spacing_eq_width, normalized_width hm, mul_one]

lemma normalized_radius {m : ℕ} (hm : 0 < m) : turnRadius (100 * m) m = 50 := by
  rw [turnRadius_eq_width, normalized_width hm, mul_one]

lemma normal_straight_eq {m : ℕ} (hm : 0 < m) (j : ℕ) (u a : ℝ) :
    straightPiece m j u + (a : ℂ) * Complex.I * straightTangent j =
      columnPoint 0 (100 * m) m j (side j * (-100 * m + u)) a := by
  apply Complex.ext <;>
    simp only [straightPiece, straightTangent, columnPoint, columnOffset,
      normalized_spacing hm, normalized_width hm, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im] <;> ring

lemma normal_circular_eq {m : ℕ} (hm : 0 < m) (j : ℕ) (u a : ℝ) :
    circularPiece m j u + (a : ℂ) * Complex.I * circularTangent j u =
      turnPoint 0 (100 * m) m j (u / 50) a := by
  apply Complex.ext
  · simp only [circularPiece, circularTangent, turnPoint, columnOffset,
      normalized_spacing hm, normalized_radius hm, normalized_width hm,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re]
    ring
  · simp only [circularPiece, circularTangent, turnPoint, columnOffset,
      normalized_spacing hm, normalized_radius hm, normalized_width hm,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_im]
    ring_nf
    rw [side_sq]
    ring

lemma straight_height_bound (m j : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (200 * m)) :
    |side j * (-100 * m + u)| ≤ 100 * m := by
  rw [abs_mul, side_abs, one_mul]
  exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma circular_angle_bound {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (50 * Real.pi)) :
    u / 50 ∈ Icc (0 : ℝ) Real.pi := by
  constructor <;> linarith [hu.1, hu.2]

lemma turn_column_time {m : ℕ} (hm : 0 < m) (j k : ℕ) {θ y a b : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) (hy : |y| ≤ 100 * m)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (he : turnPoint 0 (100 * m) m j θ a = columnPoint 0 (100 * m) m k y b) :
    columnEntry 0 m j + 200 * m + 50 * θ =
      columnEntry 0 m k + (side k * y + 100 * m) ∧ a = b := by
  have hh : (0 : ℝ) < 100 * m := by positivity
  rcases turnPoint_column_gluing hh hm 0 hθ hy ha hb he with
    ⟨hθ, hk, hy, hab⟩ | ⟨hθ, hk, hy, hab⟩
  · subst θ
    subst k
    subst y
    refine ⟨?_, hab⟩
    have hs : side j * (side j * (100 * (m : ℝ))) = 100 * m := by
      rw [← mul_assoc, ← pow_two, side_sq, one_mul]
    rw [hs]
    ring
  · subst θ
    subst k
    subst y
    refine ⟨?_, hab⟩
    have hs : side (j + 1) * (side j * (100 * (m : ℝ))) = -(100 * m) := by
      rw [side_succ, neg_mul, ← mul_assoc, ← pow_two, side_sq, one_mul]
    rw [hs, columnEntry_succ]
    ring

/-- Normal coordinates over the complete finite array are injective,
including the endpoints shared by adjacent straight and circular pieces. -/
theorem array_normal_injective {m : ℕ} (hm : 0 < m) (last : ℕ) :
    InjOn (normalRibbon (arraySpine m last) (arrayTangent m last))
      {z : ℂ | z.re ∈ Icc (0 : ℝ) (arrayEnd m last) ∧ |z.im| ≤ 1} := by
  intro z hz w hw he
  have hh : (0 : ℝ) < 100 * m := by positivity
  rcases array_pieces m last hz.1 with ⟨i, _, u, hu, hzu, hzs, hzT⟩ |
    ⟨i, _, u, hu, hzu, hzs, hzT⟩ <;>
  rcases array_pieces m last hw.1 with ⟨j, _, v, hv, hwv, hws, hwT⟩ |
    ⟨j, _, v, hv, hwv, hws, hwT⟩
  · simp only [normalRibbon] at he
    rw [hzs, hzT, hws, hwT,
      normal_straight_eq hm, normal_straight_eq hm] at he
    have hij := columnPoint_equal_forces_index hh hm 0 _ _ hz.2 hw.2 he
    subst j
    obtain ⟨hy, hab⟩ := columnPoint_injective hh hm 0 i he
    have hs : side i ≠ 0 := by
      intro h
      have hh := side_abs i
      rw [h, abs_zero] at hh
      norm_num at hh
    have huv : u = v := by
      have h := mul_left_cancel₀ hs hy
      linarith
    exact Complex.ext (by rw [hzu, hwv, huv]) hab
  · simp only [normalRibbon] at he
    rw [hzs, hzT, hws, hwT,
      normal_straight_eq hm, normal_circular_eq hm] at he
    obtain ⟨ht, hab⟩ := turn_column_time hm j i (circular_angle_bound hv)
      (straight_height_bound m i hu) hw.2 hz.2 he.symm
    have hs : side i * (side i * (-100 * (m : ℝ) + u)) = -100 * m + u := by
      rw [← mul_assoc, ← pow_two, side_sq, one_mul]
    rw [hs] at ht
    exact Complex.ext (by rw [hzu, hwv]; linarith) hab.symm
  · simp only [normalRibbon] at he
    rw [hzs, hzT, hws, hwT,
      normal_circular_eq hm, normal_straight_eq hm] at he
    obtain ⟨ht, hab⟩ := turn_column_time hm i j (circular_angle_bound hu)
      (straight_height_bound m j hv) hz.2 hw.2 he
    have hs : side j * (side j * (-100 * (m : ℝ) + v)) = -100 * m + v := by
      rw [← mul_assoc, ← pow_two, side_sq, one_mul]
    rw [hs] at ht
    exact Complex.ext (by rw [hzu, hwv]; linarith) hab
  · simp only [normalRibbon] at he
    rw [hzs, hzT, hws, hwT,
      normal_circular_eq hm, normal_circular_eq hm] at he
    have hij : i = j := by
      by_contra hij
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact turnPoint_ne hh hm hij 0 (circular_angle_bound hu) (circular_angle_bound hv)
          hz.2 hw.2 he
      · exact turnPoint_ne hh hm hji 0 (circular_angle_bound hv) (circular_angle_bound hu)
          hw.2 hz.2 he.symm
    subst j
    obtain ⟨ht, hab⟩ := turnPoint_injective hh hm 0 i (circular_angle_bound hu)
      (circular_angle_bound hv) hz.2 hw.2 he
    exact Complex.ext (by rw [hzu, hwv]; linarith) hab

end SLEExactGauge.Serpentine

end

end OAI
