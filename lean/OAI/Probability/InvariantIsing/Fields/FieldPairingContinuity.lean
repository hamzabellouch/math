import OAI.Probability.InvariantIsing.Fields.FieldPairingError

namespace OAI

/-! Pairing errors for the rounded quantile paths used in the cavity
calculation. A uniform field-height bound suffices for L1 stability. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

lemma field_pairing_path_error (p q : OverlapPath) (h : FieldStep) :
    |fieldPairing p h - fieldPairing q h| ≤ h.height (Fin.last h.depth) *
      ∫ s, |p s - q s| ∂pathMeasure := by
  have hi : Integrable (fun s => (p s - q s) * fieldFunction h s) pathMeasure := by
    apply ((integrable_path_mul_field p h).sub (integrable_path_mul_field q h)).congr
    apply ae_of_all
    intro s
    change p s * fieldFunction h s - q s * fieldFunction h s = _
    ring
  have he : fieldPairing p h - fieldPairing q h =
      ∫ s, (p s - q s) * fieldFunction h s ∂pathMeasure := by
    rw [fieldPairing, fieldPairing, ← integral_sub (integrable_path_mul_field p h)
      (integrable_path_mul_field q h)]
    congr 1
    funext s
    ring
  rw [he]
  calc
    _ ≤ ∫ s, |(p s - q s) * fieldFunction h s| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, h.height (Fin.last h.depth) * |p s - q s| ∂pathMeasure := by
      apply integral_mono hi.abs (((p.integrable.sub q.integrable).abs).const_mul _)
      intro s
      dsimp only
      rw [abs_mul, abs_of_nonneg (fieldFunction_nonneg h s)]
      exact (mul_le_mul_of_nonneg_left (fieldFunction_le_last h s) (abs_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem field_pairing_path_tendsto (p : OverlapPath) (q : ℕ → OverlapPath)
    (h : ℕ → FieldStep) {C : ℝ}
    (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hq : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => fieldPairing (q n) (h n) - fieldPairing p (h n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => C * ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0) by
      simpa only [mul_zero] using hq.const_mul C)
  rw [Real.norm_eq_abs]
  exact (field_pairing_path_error (q n) p (h n)).trans
    (mul_le_mul_of_nonneg_right (hC n) (integral_nonneg (fun _ => abs_nonneg _)))

end InvariantIsing

end

end OAI
