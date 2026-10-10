import OAI.Probability.BenjaminiSchramm.BlockExposure

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E ι : Type*}

lemma measure_inter_of_separate_blocks (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdA : DependsOn (fun ω => ω ∈ A) S)
    (hdB : DependsOn (fun ω => ω ∈ B) Sᶜ) :
    law q (A ∩ B) = law q A * law q B := by
  have hBg : DependsOn (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) Sᶜ := by
    intro ω η hωη
    have h := hdB hωη
    change (ω ∈ B) = (η ∈ B) at h
    change (if ω ∈ B then (1 : ℝ≥0∞) else 0) =
      (if η ∈ B then (1 : ℝ≥0∞) else 0)
    exact congrArg (fun p : Prop => if p then (1 : ℝ≥0∞) else 0) h
  have h := lintegral_indicator_fresh q S A hA hdA
    (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) (measurable_const.indicator hB) hBg
  have heq : A.indicator (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) =
      (A ∩ B).indicator (fun _ : Set E => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  have hAB : (∫⁻ ω, (A ∩ B).indicator (fun _ : Set E => (1 : ℝ≥0∞)) ω ∂law q) =
      law q (A ∩ B) := lintegral_indicator_one (hA.inter hB)
  have hB' : (∫⁻ ω, B.indicator (fun _ : Set E => (1 : ℝ≥0∞)) ω ∂law q) =
      law q B := lintegral_indicator_one hB
  rw [heq,hAB,hB'] at h
  exact h

theorem selected_fresh_continuation_lower [Countable ι]
    (q : E → unitInterval) (S : Set E) (A B : ι → Set (Set E))
    (hmA : ∀ i, MeasurableSet (A i)) (hmB : ∀ i, MeasurableSet (B i))
    (hdA : ∀ i, DependsOn (fun ω => ω ∈ A i) S)
    (hdB : ∀ i, DependsOn (fun ω => ω ∈ B i) Sᶜ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (c : ℝ≥0∞) (hc : ∀ i, c ≤ law q (B i)) :
    law q (⋃ i, A i) * c ≤ law q (⋃ i, A i ∩ B i) := by
  have hdisj' : Pairwise (fun i j => Disjoint (A i ∩ B i) (A j ∩ B j)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [measure_iUnion hdisj hmA,measure_iUnion hdisj' (fun i => (hmA i).inter (hmB i)),
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [measure_inter_of_separate_blocks q S _ _ (hmA i) (hmB i) (hdA i) (hdB i)]
  exact mul_le_mul' le_rfl (hc i)

end CriticalPercolation.BernoulliProduct

end

end OAI
