import OAI.NumberTheory.Jacobsthal.Renewal.FiniteAdmittedOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlagWeightConjugation
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform PersistentFailureFlag SubMarkovFlagPowers FlaggedOccupationBound

variable {α : Type*} [MeasurableSpace α]

def flagWeight (w : PositiveWeight α) : PositiveWeight (FlagState α) where
  value z := w z.1
  measurable_value := w.measurable_value.comp measurable_fst
  ne_zero z := w.ne_zero z.1
  ne_top z := w.ne_top z.1

theorem marked_conjugate (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (w : PositiveWeight α) :
    marked (conjugate K w) hBad = conjugate (marked K hBad) (flagWeight w) := by
  ext z : 1
  apply Measure.ext_of_lintegral
  intro F hF
  have hRow := row_update_measurable hBad z.2
  rw [marked_eq_map_sfinite,lintegral_map hF hRow,
    conjugate_lintegral K w z.1 (F := fun y => F (y,z.2 || badBit Bad y)) (hF.comp hRow),
    conjugate_lintegral (marked K hBad) (flagWeight w) z hF,
    marked_eq_map_sfinite,
    lintegral_map (f := fun b : FlagState α => flagWeight w b / flagWeight w z * F b)
      (((flagWeight w).measurable_value.div measurable_const).mul hF) hRow]
  rfl

theorem marked_conjugate_power (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (w : PositiveWeight α) (n : ℕ) :
    (marked (conjugate K w) hBad)^n = conjugate ((marked K hBad)^n) (flagWeight w) := by
  rw [marked_conjugate]
  exact conjugate_pow (marked K hBad) (flagWeight w) n

theorem marked_conjugate_power_integral (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (w : PositiveWeight α) (n : ℕ) (z : FlagState α)
    {F : FlagState α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y,F y ∂((marked (conjugate K w) hBad)^n) z) =
      (w z.1)⁻¹*(∫⁻ y,w y.1*F y ∂((marked K hBad)^n) z) := by
  rw [marked_conjugate]
  exact conjugate_pow_lintegral (marked K hBad) (flagWeight w) n z hF

theorem selected_inverse_reward (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (w : PositiveWeight α) (n : ℕ) (z : FlagState α)
    {F : α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y,selected (fun a => F a / w a) y ∂((marked (conjugate K w) hBad)^n) z) =
      (w z.1)⁻¹*(∫⁻ y,selected F y ∂((marked K hBad)^n) z) := by
  rw [marked_conjugate_power_integral K hBad w n z
    (F := selected (fun a => F a / w a)) (selected_measurable (hF.div w.measurable_value))]
  congr 1
  apply lintegral_congr
  rintro ⟨a,b⟩
  cases b with
  | false => simp only [selected_false,mul_zero]
  | true =>
    simp only [selected_true,div_eq_mul_inv]
    rw [mul_left_comm,ENNReal.mul_inv_cancel (w.ne_zero a) (w.ne_top a),mul_one]

end NumberTheoryLean.FlagWeightConjugation

end

section

namespace NumberTheoryLean.FlaggedHarmonicTransform

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures AdmittedHarmonicPaths HarmonicWeightKernel
open KernelWeightTransform FlagWeightConjugation PersistentFailureFlag
open FlaggedOccupationBound ContinuousHighPartition OriginalHarmonicOccupation

instance tiltedFlagged_sfinite (v ell S : ℝ) : IsSFiniteKernel (tiltedFlagged v ell S) := by
  unfold tiltedFlagged
  infer_instance

theorem actual_marked_transform (v ell S : ℝ) :
    FlaggedHarmonicPaths.kernel v ell S = conjugate (tiltedFlagged v ell S) (flagWeight harmonicWeight) := by
  rw [← marked_harmonic_eq,admitted_weight_transform,marked_conjugate]
  rfl

theorem scaled_high_integral (v ell S : ℝ) (s : State) (b : Bool) (n : ℕ)
    {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*
      (∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n) ((s,0),b)) =
      ∫⁻ y,selected (fun z => gapSquaredWeight v z*F z) y ∂((tiltedFlagged v ell S)^n) ((s,0),b) := by
  rw [actual_marked_transform,conjugate_pow,conjugate_lintegral _ (flagWeight harmonicWeight) _ (selected_measurable hF),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  rintro ⟨z,b'⟩
  cases b' with
  | false => simp only [selected_false,mul_zero]
  | true =>
    simp only [selected_true]
    change ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*
      ((harmonicWeight z/harmonicWeight (s,0))*F z) = gapSquaredWeight v z*F z
    rw [← mul_assoc,scaled_ratio]

theorem high_inverse_compact_le (v ell S : ℝ) (s : State)
    {F : CostState → ℝ≥0∞} (hF : Measurable F) {D : ℝ≥0∞} (hD : D ≠ ∞) {K : ℝ}
    (hbound : ∀ z,F z ≤ D) (hsupport : ∀ z,K < RegeneratingInverseBands.gapValue v z → F z=0) :
    (∑' n : ℕ,∫⁻ y,selected (fun z => gapSquaredWeight v z*F z) y
      ∂((tiltedFlagged v ell S)^n) (FlaggedHarmonicPaths.initial S (s,0))) ≤
      ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*D*
        AdmittedHighRemoval.lowHighMass v ell S (s,0) K := by
  have he : (∑' n : ℕ,∫⁻ y,selected (fun z => gapSquaredWeight v z*F z) y
      ∂((tiltedFlagged v ell S)^n) (FlaggedHarmonicPaths.initial S (s,0))) =
      ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*
        (∑' n : ℕ,∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n)
          (FlaggedHarmonicPaths.initial S (s,0))) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    exact (scaled_high_integral v ell S s (if S < stateRatio s then true else false) n hF).symm
  rw [he,mul_assoc]
  exact mul_le_mul_of_nonneg_left (harmonic_high_compact_bound v ell S (s,0) hD hbound hsupport) zero_le

end NumberTheoryLean.FlaggedHarmonicTransform

end

end Erdos970

end OAI
