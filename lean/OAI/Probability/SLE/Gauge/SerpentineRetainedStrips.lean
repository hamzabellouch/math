import OAI.Probability.SLE.Gauge.SerpentineParameters
import OAI.Probability.SLE.Gauge.SerpentineStepCount
import OAI.Probability.SLE.Gauge.SerpentineCompleteEmbedding

namespace OAI

/-! The prescribed integer middle strips are actual straight portions
of the joined serpentine, with exactly m² distinct retained indices. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma columnEntry_mono (A : ℝ) (m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    columnEntry A m i ≤ columnEntry A m j := by
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hD : 0 ≤ 200 * (m : ℝ) + 50 * Real.pi := by positivity
  unfold columnEntry
  nlinarith

lemma array_preserves_column {m i last : ℕ} (hi : i ≤ last) {t : ℝ}
    (ht : t ≤ arrayEnd m i) :
    arraySpine m last t = arraySpine m i t ∧ arrayTangent m last t = arrayTangent m i t := by
  induction last with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    exact ⟨rfl, rfl⟩
  | succ last ih =>
    by_cases hil : i = last + 1
    · subst i; exact ⟨rfl, rfl⟩
    · have hil' : i ≤ last := by omega
      have ht' : t ≤ columnEntry 0 m last + 200 * m := by
        have he := columnEntry_mono 0 m hil'
        dsimp only [arrayEnd] at ht
        linarith
      have hc : t ≤ columnEntry 0 m (last + 1) := by
        rw [columnEntry_succ]
        linarith [Real.pi_pos]
      obtain ⟨hs, hT⟩ := ih hil'
      constructor
      · simpa only [arraySpine, curveJoin_of_le hc, curveJoin_of_le ht'] using hs
      · simpa only [arrayTangent, curveJoin_of_le hc, curveJoin_of_le ht'] using hT

lemma array_on_column {m i last : ℕ} (hi : i ≤ last) {t : ℝ}
    (ht : t ∈ Icc (columnEntry 0 m i) (arrayEnd m i)) :
    arraySpine m last t = straightPiece m i (t - columnEntry 0 m i) ∧
      arrayTangent m last t = straightTangent i := by
  obtain ⟨hs, hT⟩ := array_preserves_column hi ht.2
  rw [hs, hT, arraySpine_tail m i ht.1, arrayTangent_tail m i ht.1]
  exact ⟨rfl, rfl⟩

lemma complete_normal_on_column {m i : ℕ} (hm : 0 < m) (hi : i ≤ 2 * m)
    (H r X Y : ℝ) {z : ℂ}
    (hz : z.re - connectorEntry H r X Y ∈
      Ioo (columnEntry 0 m i) (arrayEnd m i)) :
    normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z =
      arrayCenter m X Y + columnPoint 0 (100 * m) m i
        (side i * (-100 * m + (z.re - connectorEntry H r X Y - columnEntry 0 m i))) z.im := by
  have hentry : connectorEntry H r X Y < z.re := by
    have he : 0 ≤ columnEntry 0 m i := by unfold columnEntry; positivity
    linarith [hz.1]
  rw [complete_normal_of_gt m H r X Y hentry]
  have hpart := array_on_column hi ⟨hz.1.le, hz.2.le⟩
  simp only [normalRibbon, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  rw [hpart.1, hpart.2, normal_straight_eq hm]

lemma retained_strip_on_column {m j i : ℕ} (hm : 0 < m) (hj : j < m) (hi : i < m)
    (H r X Y : ℝ) (hA : 0 ≤ connectorEntry H r X Y) {z : ℂ}
    (hz : z.re ∈ Icc
      ((retainedStep (connectorEntry H r X Y) m j i : ℝ) + 1 / 3)
      ((retainedStep (connectorEntry H r X Y) m j i : ℝ) + 2 / 3)) :
    normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z =
      arrayCenter m X Y + columnPoint 0 (100 * m) m j
        (side j * (-100 * m + (z.re - connectorEntry H r X Y - columnEntry 0 m j))) z.im := by
  apply complete_normal_on_column hm (by omega)
  have he := retained_middle_in_straight hA hi hz
  have hc : columnEntry (connectorEntry H r X Y) m j =
      connectorEntry H r X Y + columnEntry 0 m j := by unfold columnEntry; ring
  rw [hc] at he
  dsimp only [arrayEnd]
  constructor <;> linarith [he.1, he.2]

end SLEExactGauge.Serpentine

end

end OAI
