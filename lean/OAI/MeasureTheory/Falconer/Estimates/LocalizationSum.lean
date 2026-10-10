import OAI.MeasureTheory.Falconer.Estimates.EnergySplitting

namespace OAI

/-!
# Summing integrated nonstationary errors

An edge is removed only after its whole oscillatory integral has been
estimated. The cardinality loss is explicit and can be absorbed by the
arbitrary power gain. No pointwise angular truncation is introduced.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem integrated_discarded_sum_bound {X ι κ : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (K : Finset κ) (G : κ → ι → ι → Prop)
    (T : κ → ι → ι → X → ℂ)
    (hT : ∀ k ∈ K, ∀ i ∈ S, ∀ j ∈ S, Integrable (T k i j) μ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ k ∈ K, ∀ i ∈ S, ∀ j ∈ S, ¬G k i j → ‖∫ x, T k i j x ∂μ‖ ≤ ε) :
    ‖(∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, T k i j x ∂μ) -
      (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S,
        if G k i j then T k i j x else 0 ∂μ)‖ ≤ (K.card : ℝ)*S.card*S.card*ε := by
  classical
  have hfull : (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, T k i j x ∂μ) =
      ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, ∫ x, T k i j x ∂μ := by
    rw [integral_finsetSum _ (fun k hk =>
      integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (hT k hk i hi)))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hT k hk i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum _ (hT k hk i hi)
  have hpart (k : κ) (hk : k ∈ K) (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      Integrable (fun x => if G k i j then T k i j x else 0) μ := by
    by_cases h : G k i j
    · simpa only [ite_eq_left h] using hT k hk i hi j hj
    · simp only [ite_eq_right h]
      exact integrable_zero _ _ _
  have hkept : (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S,
        if G k i j then T k i j x else 0 ∂μ) =
      ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, if G k i j then (∫ x, T k i j x ∂μ) else 0 := by
    rw [integral_finsetSum _ (fun k hk =>
      integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (hpart k hk i hi)))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hpart k hk i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (hpart k hk i hi)]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hfull,hkept,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, ε := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : G k i j
      · simpa only [ite_eq_left h,sub_self,norm_zero] using hε
      · simpa only [ite_eq_right h,sub_zero] using herr k hk i hi j hj h
    _ = _ := by simp [mul_assoc]

end Falconer

end OAI
