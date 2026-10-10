import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

namespace Yau
open Set MeasureTheory
noncomputable section

lemma integral_le_finite_cover {E ι : Type*} [MeasurableSpace E]
    {μ : Measure E} {Q : Set E} (hQ : MeasurableSet Q) {s : E → ℝ}
    (hs : IntegrableOn s Q μ) (t : Finset ι) (B : ι → Set E) (c : ι → ℝ)
    (hB : ∀ i ∈ t, MeasurableSet (B i)) (hfin : ∀ i ∈ t, μ (B i) ≠ ⊤)
    (hc : ∀ i ∈ t, 0 ≤ c i) (hcov : Q ⊆ ⋃ i ∈ t, B i)
    (hbound : ∀ i ∈ t, ∀ x ∈ Q ∩ B i, s x ≤ c i) :
    (∫ x in Q, s x ∂μ) ≤ ∑ i ∈ t, μ.real (B i)*c i := by
  classical
  have hi : ∀ i ∈ t, Integrable ((B i).indicator (fun _ ↦ c i)) μ := by
    intro i hit
    exact (integrable_indicator_iff (hB i hit)).mpr (integrableOn_const (hfin i hit))
  have hm : ∀ x, Q.indicator s x ≤ ∑ i ∈ t, (B i).indicator (fun _ ↦ c i) x := by
    intro x
    have hn : ∀ i ∈ t, 0 ≤ (B i).indicator (fun _ ↦ c i) x :=
      fun i hit ↦ indicator_nonneg (fun _ _ ↦ hc i hit) x
    by_cases hx : x ∈ Q
    · obtain ⟨i,hit,hxi⟩ := mem_iUnion₂.mp (hcov hx)
      rw [indicator_of_mem hx]
      apply (hbound i hit x ⟨hx,hxi⟩).trans
      calc
        c i = (B i).indicator (fun _ ↦ c i) x := (indicator_of_mem hxi (fun _ ↦ c i)).symm
        _ ≤ _ := Finset.single_le_sum hn hit
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg hn
  have hh := integral_mono ((integrable_indicator_iff hQ).mpr hs)
    (integrable_finsetSum t hi) hm
  rw [integral_indicator hQ,integral_finsetSum t hi] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i hit
  rw [integral_indicator (hB i hit),setIntegral_const,smul_eq_mul]

end
end Yau

end OAI
