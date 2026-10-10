import OAI.Geometry.NodalSets.Elliptic.FiniteCertificateWeight

namespace OAI

namespace Yau
open Set MeasureTheory
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exists_good_successful_tests (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hT : 0 < ∑ i, w i) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : 0 < c) (hprob : ∀ i, c ≤ μ.real (A i))
    (Q : Set Ω) (hQ : MeasurableSet Q) (hfail : (μ Qᶜ).toReal < c/2) :
    ∃ a ∈ Q, ∃ u : Finset ι, (∀ i ∈ u, a ∈ A i) ∧
      c*(∑ i, w i)/2 ≤ ∑ i ∈ u, w i := by
  classical
  obtain ⟨a,ha,hweight⟩ := exists_good_successful_test_weight w hw hT A hA hc hprob Q hQ hfail
  refine ⟨a,ha,Finset.univ.filter (fun i ↦ a ∈ A i),?_,?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · convert hweight using 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a ∈ A i <;> simp [hi]

end
end Yau

end OAI
