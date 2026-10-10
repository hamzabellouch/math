import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightSlab

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalized_restriction_contact_le {Ω : Type*} [MeasurableSpace Ω]
    (μ η : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (D C A R : Set Ω) (hC : MeasurableSet C)
    (hA : MeasurableSet A) (hAR : A ⊆ R) (c γ δ : ℝ≥0∞)
    (hc : 0 < c) (hcD : c ≤ μ D) (hη : η D ≤ μ D+γ)
    (hδ : η (R \ D) ≤ δ) (he : μ (A \ C) = η (A \ C)) :
    normalizedMeasure (μ.restrict D) A ≤ normalizedMeasure (η.restrict D) A +
      normalizedMeasure (μ.restrict D) C + c⁻¹*(γ+δ) := by
  have ha : μ D ≠ 0 := ne_of_gt (hc.trans_le hcD)
  have hfin : μ D ≠ ⊤ := measure_ne_top _ _
  have hmass : ∀ (ξ : Measure Ω), ξ.restrict D Set.univ = ξ D := by
    intro ξ
    rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  have hraw : μ (A ∩ D) ≤ μ (C ∩ D) + η (A ∩ D) + δ := by
    calc
      _ ≤ μ (C ∩ D)+μ (A \ C) := by
        apply (measure_mono (s := A ∩ D) (t := (C ∩ D) ∪ (A \ C)) ?_).trans (measure_union_le _ _)
        intro z hz
        by_cases hzC : z ∈ C
        · exact Or.inl ⟨hzC,hz.2⟩
        · exact Or.inr ⟨hz.1,hzC⟩
      _ = μ (C ∩ D)+η (A \ C) := by rw [he]
      _ ≤ μ (C ∩ D)+(η (A ∩ D)+δ) := by
        apply add_le_add le_rfl
        calc
          _ ≤ η ((A ∩ D) ∪ (R \ D)) := by
            apply measure_mono
            intro z hz
            by_cases hzD : z ∈ D
            · exact Or.inl ⟨hz.1,hzD⟩
            · exact Or.inr ⟨hAR hz.1,hzD⟩
          _ ≤ η (A ∩ D)+η (R \ D) := measure_union_le _ _
          _ ≤ _ := add_le_add le_rfl hδ
      _ = _ := (add_assoc _ _ _).symm
  have hηA : (η.restrict D) A ≤ (μ D+γ)* normalizedMeasure (η.restrict D) A := by
    by_cases hz : η D = 0
    · have hzero : η (A ∩ D) = 0 := measure_mono_null Set.inter_subset_right hz
      rw [Measure.restrict_apply hA,hzero]
      exact zero_le
    · have heq : (η.restrict D) A = η D * normalizedMeasure (η.restrict D) A := by
        change _ = η D*((η.restrict D Set.univ)⁻¹*(η.restrict D) A)
        rw [hmass,← mul_assoc,ENNReal.mul_inv_cancel hz (measure_ne_top _ _),one_mul]
      rw [heq]
      exact mul_le_mul_left hη _
  have hprob : normalizedMeasure (η.restrict D) A ≤ 1 := by
    by_cases hz : η D = 0
    · change (η.restrict D Set.univ)⁻¹*(η.restrict D) A ≤ 1
      rw [hmass,Measure.restrict_apply hA,measure_mono_null Set.inter_subset_right hz]
      simp
    · let := normalizedMeasure_probability (η.restrict D) (by rw [hmass]; exact hz)
      exact prob_le_one
  have hmid : μ (A ∩ D) ≤ μ D * (normalizedMeasure (η.restrict D) A +
      normalizedMeasure (μ.restrict D) C) + (γ+δ) := by
    calc
      _ ≤ μ (C ∩ D) + (μ D+γ)*normalizedMeasure (η.restrict D) A + δ :=
        hraw.trans (add_le_add (add_le_add le_rfl (by simpa only [Measure.restrict_apply hA] using hηA)) le_rfl)
      _ ≤ μ (C ∩ D) + (μ D*normalizedMeasure (η.restrict D) A+γ) + δ := by
        rw [add_mul]
        exact add_le_add (add_le_add le_rfl (add_le_add le_rfl
          (by simpa only [mul_one] using mul_le_mul_right hprob γ))) le_rfl
      _ = _ := by
        have hCeq : μ D * normalizedMeasure (μ.restrict D) C = μ (C ∩ D) := by
          change μ D*((μ.restrict D Set.univ)⁻¹*(μ.restrict D) C) = _
          rw [hmass,← mul_assoc,ENNReal.mul_inv_cancel ha hfin,one_mul,Measure.restrict_apply hC]
        rw [mul_add,hCeq]
        ac_rfl
  change (μ.restrict D Set.univ)⁻¹*(μ.restrict D) A ≤ _
  rw [hmass,Measure.restrict_apply hA]
  calc
    _ ≤ (μ D)⁻¹*(μ D*(normalizedMeasure (η.restrict D) A+normalizedMeasure (μ.restrict D) C)+(γ+δ)) :=
      mul_le_mul_right hmid _
    _ = normalizedMeasure (η.restrict D) A + normalizedMeasure (μ.restrict D) C + (μ D)⁻¹*(γ+δ) := by
      rw [mul_add,← mul_assoc,ENNReal.inv_mul_cancel ha hfin,one_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_left (ENNReal.inv_le_inv.mpr hcD) _)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
