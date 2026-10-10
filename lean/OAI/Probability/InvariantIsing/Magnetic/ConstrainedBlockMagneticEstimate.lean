import OAI.Probability.InvariantIsing.Magnetic.ConstrainedBlockBias

namespace OAI

/-! Finite constrained-block comparison with the actual scalar magnetic
functional. Every error term is independent of the cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma sum_sites_group {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (f : A → ℝ) :
    (∑ i, f (group i)) = ∑ a, spinGroupSize group a * f a := by
  rw [← Finset.sum_fiberwise Finset.univ group]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => group i = a), f a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp [spinGroupSize]

lemma spinGroupFieldConstant_of_means {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (m bias : A → ℝ)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2)) :
    spinGroupFieldConstant group k bias = ∑ i, bias (group i) * m (group i) := by
  rw [sum_sites_group group (fun a => bias a * m a)]
  unfold spinGroupFieldConstant
  apply Finset.sum_congr rfl
  intro a _
  rw [hc a]
  ring

theorem biasedConstrainedBlockValue_gap {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    0 ≤ biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b ∧
      biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b ≤
        (N : ℝ)⁻¹ * (∫ y, restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
          ∂fieldCanonicalVectorLaw N h b) := by
  have hF := restrictedFieldRecursion_biased_root_integrable hN Finset.univ Finset.univ_nonempty h b
  have hS' := restrictedFieldRecursion_biased_root_integrable hN S hS h b
  have he : biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b =
      (N : ℝ)⁻¹ * (∫ z, restrictedFieldRecursion Finset.univ h.depth (chainExponent h.cut)
        (fieldStepVariance h) z - restrictedFieldRecursion S h.depth (chainExponent h.cut)
        (fieldStepVariance h) z
        ∂Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) := by
    rw [integral_sub hF hS']
    unfold biasedConstrainedBlockValue
    ring
  rw [he]
  constructor
  · apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro z
    apply sub_nonneg.mpr
    exact restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
      (Finset.subset_univ _) _ _ _
      (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1) z
  · exact mul_le_mul_of_nonneg_left (restrictedFieldRecursion_root_loss hN S hS h b) (by positivity)

lemma magneticBlockGap_eq_biasedGap {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2)) (h : FieldStep) :
    (N : ℝ)⁻¹ * (∑ i, constrainedFieldValue h (m (group i))) -
        constrainedBlockValue (spinGroupSlice group k) h =
      biasedConstrainedBlockValue Finset.univ h (fun i => magneticBias h (m (group i))) -
        biasedConstrainedBlockValue (spinGroupSlice group k) h (fun i => magneticBias h (m (group i))) := by
  rw [biasedConstrainedBlockValue_univ hN,
    biasedConstrainedBlockValue_group hN group k hk (fun a => magneticBias h (m a)),
    spinGroupFieldConstant_of_means group k m (fun a => magneticBias h (m a)) hc]
  simp_rw [constrainedFieldValue_magneticBias h (hm _)]
  rw [Finset.sum_sub_distrib]
  ring

theorem magneticBlockGap_estimate {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2))
    (h : FieldStep) {B H ε t : ℝ} (hB : ∀ i, |magneticBias h (m (group i))| ≤ B)
    (hH : h.height (Fin.last h.depth) ≤ H) (hε : 0 < ε) (ht : 0 ≤ t) :
    0 ≤ (N : ℝ)⁻¹ * (∑ i, constrainedFieldValue h (m (group i))) -
        constrainedBlockValue (spinGroupSlice group k) h ∧
      (N : ℝ)⁻¹ * (∑ i, constrainedFieldValue h (m (group i))) -
        constrainedBlockValue (spinGroupSlice group k) h ≤
      (N : ℝ)⁻¹ * (ε * (N * (2 * Real.exp (2 * B + 4 * H))) +
        (ε⁻¹ + t) * (Fintype.card A * Real.sqrt N) + N * Real.log (1 + Real.exp (-t))) := by
  rw [magneticBlockGap_eq_biasedGap hN group k hk m hm hc]
  have hg := biasedConstrainedBlockValue_gap hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h (fun i => magneticBias h (m (group i)))
  refine ⟨hg.1, hg.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he := magnetic_block_terminal_loss_size group k hk m hm hc h hB hH hε ht
  simpa only [restrictedFieldTerminal_univ] using he

end InvariantIsing

end

end OAI
