import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # The mean probability of the two original endpoint laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

noncomputable def meanProbability (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X := by
  let ρ : Measure X := (2:ℝ≥0∞)⁻¹ • ((μ : Measure X)+(ν : Measure X))
  have : IsProbabilityMeasure ρ := by
    constructor
    simp only [ρ,Measure.smul_apply,Measure.add_apply,measure_univ,smul_eq_mul]
    rw [show (1:ℝ≥0∞)+1=2 by norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  exact ⟨ρ,this⟩

theorem meanProbability_apply (μ ν : ProbabilityMeasure X) (A : Set X) :
    (meanProbability μ ν : Measure X) A = (2:ℝ≥0∞)⁻¹ *
      ((μ : Measure X) A+(ν : Measure X) A) := rfl

theorem meanProbability_ae (μ ν : ProbabilityMeasure X) (P : X → Prop)
    (hμ : ∀ᵐ x ∂(μ : Measure X), P x) (hν : ∀ᵐ x ∂(ν : Measure X), P x) :
    ∀ᵐ x ∂(meanProbability μ ν : Measure X), P x :=
  Measure.ae_smul_measure (ae_add_measure_iff.mpr ⟨hμ,hν⟩) _

theorem meanProbability_frostman {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    {s C : ℝ} (hμ : FrostmanBallBound (μ : Measure (Space d)) s C) (hν : FrostmanBallBound (ν : Measure (Space d)) s C) :
    FrostmanBallBound (meanProbability μ ν : Measure (Space d)) s C := by
  intro x r hr
  rw [meanProbability_apply]
  apply (mul_le_mul_right (add_le_add (hμ x r hr) (hν x r hr)) _).trans_eq
  rw [← two_mul,← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]

theorem meanProbability_heavy (μ ν : ProbabilityMeasure X) (A : Set X) (m : ℝ)
    (h : ENNReal.ofReal (2*m) ≤ (μ : Measure X) A+(ν : Measure X) A) :
    ENNReal.ofReal m ≤ (meanProbability μ ν : Measure X) A := by
  rw [meanProbability_apply]
  have hh := mul_le_mul_right h ((2:ℝ≥0∞)⁻¹)
  rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat,← mul_assoc] at hh
  norm_num only [ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞),one_mul] at hh
  exact hh

end Falconer

end OAI
