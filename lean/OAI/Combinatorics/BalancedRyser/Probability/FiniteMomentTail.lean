import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

noncomputable section
open MeasureTheory
open scoped Classical
namespace Balanced
open scoped _root_.Balanced

theorem upper_tail_of_centered_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (m A q C : ℝ) (s : ℕ) (hq : 0 < q)
    (hm : m ≤ A * q)
    (hi : Integrable (fun ω => |X ω - m| ^ (2*s)) μ)
    (hbound : (∫ ω, |X ω - m| ^ (2*s) ∂μ) ≤ C * q^s) :
    μ.real {ω | (A+1)*q < X ω} ≤ C / q^s := by
  have hsub : {ω | (A+1)*q < X ω} ⊆
      {ω | q^(2*s) ≤ |X ω-m|^(2*s)} := by
    intro ω hω
    have hd : q ≤ |X ω-m| :=
      (by change (A+1)*q < X ω at hω; linarith : q ≤ X ω-m).trans (le_abs_self _)
    exact pow_le_pow_left₀ hq.le hd (2*s)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => |X ω-m|^(2*s))
    (Filter.Eventually.of_forall (fun _ => by positivity)) hi (q^(2*s))
  have hmul : q^(2*s) * μ.real {ω | (A+1)*q < X ω} ≤ C*q^s :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      (hmarkov.trans hbound)
  calc
    _ ≤ (C*q^s) / q^(2*s) := by
      apply (le_div_iff₀ (pow_pos hq (2*s))).mpr
      simpa only [mul_comm] using hmul
    _ = C / q^s := by
      rw [two_mul, pow_add]
      field_simp

namespace PatternModel

theorem measureReal_le_of_fixed_indicator_bound (P : PatternModel)
    (K : Finset P.Color) (x : P.Sample) (E : Set P.Sample)
    (hE : MeasurableSet E) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a, P.fixedExpectation K a (E.indicator (fun _ => (1 : ℝ))) ≤ B) :
    P.measure.real E ≤ B := by
  let : IsProbabilityMeasure P.measure := by
    dsimp [measure]
    infer_instance
  have hempty (ω : P.Sample) : P.fixCoordinates ∅ x ω = ω := by
    funext c
    simp [fixCoordinates]
  have h := P.fixedExpectation_mul_le_of_fixedBounds ∅ K x
    (fun _ => 1) (E.indicator (fun _ => (1 : ℝ))) B 1 1 hB
    measurable_const (measurable_const.indicator hE)
    (fun _ => zero_le_one) (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (fun _ => le_rfl)
    (fun ω => by by_cases hω : ω ∈ E <;> simp [hω])
    (fun _ _ _ => rfl)
    (by simpa only [Finset.empty_union] using hbound)
  simpa [fixedExpectation, hempty, integral_indicator_const, hE] using h

end PatternModel
end Balanced

end

end OAI
