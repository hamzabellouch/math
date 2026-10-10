import OAI.Geometry.NodalSets.Elliptic.CertificateSelection

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

def successfulTestWeight (w : ι → ℝ) (A : ι → Set Ω) (a : Ω) : ℝ :=
  ∑ i, (A i).indicator (fun _ ↦ w i) a

omit [MeasurableSpace Ω] in
lemma successfulTestWeight_bounds (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ι → Set Ω) (a : Ω) :
    0 ≤ successfulTestWeight w A a ∧ successfulTestWeight w A a ≤ ∑ i, w i := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact indicator_nonneg (fun _ _ ↦ hw i) a
  · apply Finset.sum_le_sum
    intro i _
    by_cases h : a ∈ A i <;> simp [h,hw i]

lemma successfulTestWeight_integrable (w : ι → ℝ) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) : Integrable (successfulTestWeight w A) μ := by
  unfold successfulTestWeight
  exact integrable_finsetSum _ (fun i _ ↦ (integrable_const (w i)).indicator (hA i))

lemma successfulTestWeight_integral (w : ι → ℝ) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫ a, successfulTestWeight w A a ∂μ) = ∑ i, μ.real (A i)*w i := by
  unfold successfulTestWeight
  rw [integral_finsetSum _ (fun i _ ↦ (integrable_const (w i)).indicator (hA i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hA i),setIntegral_const,smul_eq_mul]

lemma exists_good_successful_test_weight (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hT : 0 < ∑ i, w i) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : 0 < c) (hprob : ∀ i, c ≤ μ.real (A i))
    (Q : Set Ω) (hQ : MeasurableSet Q) (hfail : (μ Qᶜ).toReal < c/2) :
    ∃ a ∈ Q, c*(∑ i, w i)/2 ≤ successfulTestWeight w A a := by
  apply exists_good_certificate_weight (successfulTestWeight_integrable w A hA) hQ hT hc
    (fun a ↦ (successfulTestWeight_bounds w hw A a).2) _ hfail
  rw [successfulTestWeight_integral w A hA,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hprob i) (hw i))

end
end Yau

end OAI
