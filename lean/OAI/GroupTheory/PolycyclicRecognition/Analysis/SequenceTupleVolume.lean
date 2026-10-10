import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Volume rates in the endpoint-tuple projection

A fixed positive thickening cell and subexponential auxiliary volume
preserve the exponential lower rate of the number of separated tuples.
-/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

theorem tuple_region_volume_subexponential
    {D : Type*} [MeasurableSpace D] (ν : Measure D) [SigmaFinite ν]
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (B : ℕ → Set D) (hBfinite : ∀ n, ν (B n) ≠ ⊤)
    (hB : HasSubexponentialUpperBoundSeq scale (fun n => (ν (B n)).toReal)) (h : ℕ) :
    let Q := fun n => {d : Fin h → D | ∀ i, d i ∈ B n}
    (∀ n, (Measure.pi fun _ : Fin h => ν) (Q n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale
        (fun n => ((Measure.pi fun _ : Fin h => ν) (Q n)).toReal) := by
  have hvol (n : ℕ) : (Measure.pi fun _ : Fin h => ν)
      {d : Fin h → D | ∀ i, d i ∈ B n} = (ν (B n)) ^ h := by
    have he : {d : Fin h → D | ∀ i, d i ∈ B n} = Set.pi univ (fun _ => B n) := by
      ext d
      simp
    rw [he, Measure.pi_pi]
    simp
  constructor
  · intro n
    rw [hvol]
    exact ENNReal.pow_ne_top (hBfinite n)
  · simpa only [hvol, ENNReal.toReal_pow] using
      hB.pow hs (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) h

theorem lower_volume_rate_of_tuple_count
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (N : ℕ → ℕ) (A B : ℕ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcfinite : c ≠ ⊤)
    (hAfinite : ∀ n, A n ≠ ⊤) (hBfinite : ∀ n, B n ≠ ⊤)
    (hB : HasSubexponentialUpperBoundSeq scale (fun n => (B n).toReal))
    {p : ℝ}
    (hN : HasSubexponentialLowerBoundSeq scale
      (fun n => (N n : ℝ) / Real.exp (scale n * p)))
    (hbound : ∀ n, (N n : ℝ≥0∞) * c ≤ A n * B n) :
    HasSubexponentialLowerBoundSeq scale (fun n => (A n).toReal / Real.exp (scale n * p)) := by
  have hc := sequence_subexponential_lower_const hs (ENNReal.toReal_pos hc0 hcfinite)
  have hden := hB.add (sequence_subexponential_upper_const hs 1) hs
  apply ((hN.mul hc).div hden
    (Eventually.of_forall (fun n => by positivity))).mono
  apply Eventually.of_forall
  intro n
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (hAfinite n) (hBfinite n)) (hbound n)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hb
  apply (div_le_iff₀ (show 0 < (B n).toReal + 1 by positivity)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr
  have hA0 : 0 ≤ (A n).toReal := ENNReal.toReal_nonneg
  nlinarith

end PolycyclicRecognition

end OAI
