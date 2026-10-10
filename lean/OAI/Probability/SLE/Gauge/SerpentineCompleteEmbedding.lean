import OAI.Probability.SLE.Gauge.SerpentineCompleteCurve
import OAI.Probability.SLE.Gauge.SerpentineAttachments
import OAI.Probability.SLE.Geometry.RoundedConnectorRegion

namespace OAI

/-! The low connector and the complete infinite array have one common
normal cross-section. Hence the entire prescribed ribbon is embedded. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma complete_normal_of_le (m : ℕ) (H r X Y : ℝ) {z : ℂ}
    (hz : z.re ≤ connectorEntry H r X Y) :
    normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z =
      normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z := by
  simp only [normalRibbon, completeSpine, completeTangent, curveJoin_of_le hz]

lemma complete_normal_of_gt (m : ℕ) (H r X Y : ℝ) {z : ℂ}
    (hz : connectorEntry H r X Y < z.re) :
    normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z =
      arrayCenter m X Y + normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m))
        (z - (connectorEntry H r X Y : ℂ)) := by
  simp only [normalRibbon, completeSpine, completeTangent, curveJoin_of_gt hz,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  abel

lemma complete_normal_cross_disjoint {m : ℕ} (hm : 0 < m) {H r X Y : ℝ}
    (hr : 50 ≤ r) (hX : 2 * r < X) (hY : H + 2 * r + 1 + 300 * m < Y)
    {z w : ℂ} (hz : 0 ≤ z.re ∧ |z.im| ≤ 1) (hwa : |w.im| ≤ 1)
    (hzA : z.re ≤ connectorEntry H r X Y) (hwA : connectorEntry H r X Y < w.re) :
    normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z ≠
      normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) w := by
  intro he
  rw [complete_normal_of_le m H r X Y hzA, complete_normal_of_gt m H r X Y hwA] at he
  let w' := w - (connectorEntry H r X Y : ℂ)
  have hw' : 0 ≤ w'.re ∧ |w'.im| ≤ 1 := by
    dsimp [w']
    simp only [sub_zero]
    exact ⟨by linarith, hwa⟩
  have hr1 : 1 < r := by linarith
  by_cases hz4 : z.re ≤ connectorFourth H r X
  · have hlo := lowConnector_normal_im_upper hr1 hX hz4 hz.2
    have hhi := array_normal_im_lower hm hw'
    have him := congrArg Complex.im he
    simp only [arrayCenter, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at him
    change -(400 * (m : ℝ)) ≤ (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) w').im at hhi
    change (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z).im =
      Y + 100 * m + (normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) w').im at him
    linarith
  · have hz4' : connectorFourth H r X < z.re := lt_of_not_ge hz4
    let y := H + 2 * r + (z.re - connectorFourth H r X) - Y - 100 * m
    have hy : y ≤ -(100 * (m : ℝ)) := by
      dsimp [y]
      dsimp only [connectorEntry] at hzA
      linarith
    have hpoint : normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) w' =
        columnPoint 0 (100 * m) m 0 y z.im := by
      have hs := congrArg (fun q : ℂ => q - arrayCenter m X Y) he
      simp only [add_sub_cancel_left] at hs
      rw [normalRibbon, (lowConnector_after hz4').1, (lowConnector_after hz4').2] at hs
      have heq : normalRibbon (arraySpine m (2 * m)) (arrayTangent m (2 * m)) w' =
          connectorTail H r X z.re + (z.im : ℂ) * Complex.I * Complex.I - arrayCenter m X Y := by
        exact hs.symm
      rw [heq]
      have hs0 : side 0 = 1 := by simp [side]
      apply Complex.ext <;>
        simp only [connectorTail, arrayCenter, columnPoint, columnOffset, Nat.cast_zero,
          zero_mul, hs0, one_mul, normalized_width hm, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im, y] <;> ring
    have hzero := (array_downward_attachment hm hw' hy hz.2 hpoint).1
    dsimp [w'] at hzero
    linarith

/-- Global embedding of the whole explicit normal ribbon, including its
real-boundary connector and infinite final vertical continuation. -/
theorem complete_normal_injective {m : ℕ} (hm : 0 < m) {H r X Y : ℝ}
    (hr : 50 ≤ r) (hX : 2 * r < X) (hY : H + 2 * r + 1 + 300 * m < Y) :
    InjOn (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y))
      {z : ℂ | 0 ≤ z.re ∧ |z.im| ≤ 1} := by
  intro z hz w hw he
  by_cases hzA : z.re ≤ connectorEntry H r X Y
  · by_cases hwA : w.re ≤ connectorEntry H r X Y
    · rw [complete_normal_of_le m H r X Y hzA, complete_normal_of_le m H r X Y hwA] at he
      exact lowConnector_normal_injective hr hX hz hw he
    · exact (complete_normal_cross_disjoint hm hr hX hY hz hw.2 hzA (lt_of_not_ge hwA) he).elim
  · by_cases hwA : w.re ≤ connectorEntry H r X Y
    · exact (complete_normal_cross_disjoint hm hr hX hY hw hz.2 hwA (lt_of_not_ge hzA) he.symm).elim
    · rw [complete_normal_of_gt m H r X Y (lt_of_not_ge hzA),
        complete_normal_of_gt m H r X Y (lt_of_not_ge hwA)] at he
      have he' := add_left_cancel he
      have hz' : 0 ≤ (z - (connectorEntry H r X Y : ℂ)).re ∧
          |(z - (connectorEntry H r X Y : ℂ)).im| ≤ 1 := by
        simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
        exact ⟨by linarith, hz.2⟩
      have hw' : 0 ≤ (w - (connectorEntry H r X Y : ℂ)).re ∧
          |(w - (connectorEntry H r X Y : ℂ)).im| ≤ 1 := by
        simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
        exact ⟨by linarith, hw.2⟩
      exact sub_left_injective (array_normal_injective_infinite hm hz' hw' he')

end SLEExactGauge.Serpentine

end

end OAI
