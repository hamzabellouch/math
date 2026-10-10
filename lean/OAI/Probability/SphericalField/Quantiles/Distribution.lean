import Mathlib
import OAI.Probability.SphericalField.Entropy.StepIntegral

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma quantileTrial_eq_integral (q : Time → Time) (hq : Measurable q) (t : Time) :
    quantileTrial q t=∫ u, (if q u ≤ t then (1:ℝ) else 0) ∂timeLaw := by
  change timeLaw.real {u | q u ≤ t}=∫ u, {u | q u ≤ t}.indicator (fun _ => (1:ℝ)) u ∂timeLaw
  rw [integral_indicator (measurableSet_le hq measurable_const),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

lemma tailIntegral_quantileTrial (q : Time → Time) (hq : Measurable q) (t : Time) :
    tailIntegral (quantileTrial q) t=quantileTail q (t:ℝ) := by
  have hm : Measurable (fun p : Time×Time => if q p.2 ≤ p.1 then (1:ℝ) else 0) :=
    measurable_const.ite (measurableSet_le (hq.comp measurable_snd) measurable_fst) measurable_const
  have hi : Integrable (fun p : Time×Time => if q p.2 ≤ p.1 then (1:ℝ) else 0)
      ((timeLaw.restrict (Ici t)).prod timeLaw) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) hm.aestronglyMeasurable
    exact ae_of_all _ fun p => by split_ifs <;> norm_num
  unfold tailIntegral
  simp_rw [quantileTrial_eq_integral q hq]
  rw [integral_integral_swap hi]
  simp_rw [timeTail_atom_integral (q _) t 1,one_mul]
  rfl

lemma quantileTail_upper (q : Time → Time) (hq : Measurable q) (t : ℝ) :
    quantileTail q t ≤ 1-t := by
  have h := integral_mono (quantileTail_integrable q hq t) (integrable_const (1-t))
    (fun u => sub_le_sub_left (le_max_right (q u:ℝ) t) 1)
  simpa [quantileTail] using h

lemma quantileTail_of_le (q : Time → Time) {t : ℝ} (ht : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ t) :
    quantileTail q t=1-t := by
  unfold quantileTail
  calc
    _ = ∫ _ : Time, (1-t) ∂timeLaw := integral_congr_ae (ht.mono fun u hu => by rw [max_eq_right hu])
    _ = _ := by simp

end SphericalPerceptron
end
end

end OAI
