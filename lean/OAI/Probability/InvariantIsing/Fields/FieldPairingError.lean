import OAI.Probability.InvariantIsing.Fields.FieldFiniteDomain
import OAI.Probability.InvariantIsing.Fields.FieldMagnetization

namespace OAI

/-! The quantitative error between the physical field derivative and the
pairing with the trial overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma field_pairing_support_error (p : OverlapPath) (h k : FieldStep) :
    |fieldPairing p k - fieldPairing p h -
      ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure| ≤
      (k.height (Fin.last k.depth) + h.height (Fin.last h.depth)) *
        ∫ s, |fieldMagnetizationPath h s - p s| ∂pathMeasure := by
  let B := fieldMagnetizationPath h
  let D := fun s => fieldFunction k s - fieldFunction h s
  have hiB : Integrable (fun s => B s * D s) pathMeasure := by
    apply ((integrable_path_mul_field B k).sub (integrable_path_mul_field B h)).congr
    apply ae_of_all
    intro s
    change B s * fieldFunction k s - B s * fieldFunction h s = B s * D s
    dsimp only [D]
    ring
  have hip : Integrable (fun s => p s * D s) pathMeasure := by
    apply ((integrable_path_mul_field p k).sub (integrable_path_mul_field p h)).congr
    apply ae_of_all
    intro s
    change p s * fieldFunction k s - p s * fieldFunction h s = p s * D s
    dsimp only [D]
    ring
  have he : fieldPairing p k - fieldPairing p h -
      (∫ s, B s * D s ∂pathMeasure) = ∫ s, (p s - B s) * D s ∂pathMeasure := by
    rw [fieldPairing, fieldPairing, ← integral_sub (integrable_path_mul_field p k)
      (integrable_path_mul_field p h)]
    simp_rw [← mul_sub]
    rw [← integral_sub hip hiB]
    congr 1
    funext s
    ring
  have hiabs : Integrable (fun s => |B s - p s|) pathMeasure := (B.integrable.sub p.integrable).abs
  have hib := hiabs.const_mul (k.height (Fin.last k.depth) + h.height (Fin.last h.depth))
  rw [he]
  calc
    _ ≤ ∫ s, |(p s - B s) * D s| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, (k.height (Fin.last k.depth) + h.height (Fin.last h.depth)) * |B s - p s|
        ∂pathMeasure := by
      apply integral_mono ((hip.sub hiB).congr (ae_of_all _ (fun s => by
        dsimp only [Pi.sub_apply]
        ring))).abs hib
      intro s
      dsimp only
      rw [abs_mul, abs_sub_comm (p s) (B s)]
      have hD : |D s| ≤ k.height (Fin.last k.depth) + h.height (Fin.last h.depth) := by
        dsimp only [D]
        exact (abs_sub _ _).trans (by
          rw [abs_of_nonneg (fieldFunction_nonneg k s), abs_of_nonneg (fieldFunction_nonneg h s)]
          exact add_le_add (fieldFunction_le_last k s) (fieldFunction_le_last h s))
      exact (mul_le_mul_of_nonneg_left hD (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

lemma field_trial_le_of_support (p : OverlapPath) (h k : FieldStep)
    (hsupport : fieldValue k 0 ≤ fieldValue h 0 -
      (∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure) / 2) :
    fieldValue k 0 + fieldPairing p k / 2 ≤ fieldValue h 0 + fieldPairing p h / 2 +
      (k.height (Fin.last k.depth) + h.height (Fin.last h.depth)) / 2 *
        ∫ s, |fieldMagnetizationPath h s - p s| ∂pathMeasure := by
  have hb := (abs_le.mp (field_pairing_support_error p h k)).2
  linarith

end InvariantIsing

end

end OAI
