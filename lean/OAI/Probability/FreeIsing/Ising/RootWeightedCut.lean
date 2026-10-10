import OAI.Probability.FreeIsing.Ising.RootAttenuation

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootWeightedCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingRootAttenuation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def extensionAverage (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (stem : List (Fin d)) (n k : ℕ) : Paths d → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun x =>
    rootAttenuation hbeta t (endpoint s) x ^ k)

theorem measurable_extensionAverage (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (stem : List (Fin d)) (n k : ℕ) :
    Measurable (extensionAverage hbeta t stem n k) := by
  unfold extensionAverage WeightedOrbitAverage.average
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun s _ =>
    (measurable_rootAttenuation hbeta t (endpoint s)).pow_const k)

theorem extensionAverage_mem_Icc (hbeta : 0 ≤ beta) (t : ℝ≥0)
    {stem : List (Fin d)} {n : ℕ} (s₀ : Extension stem n) (k : ℕ) (x : Paths d) :
    0 ≤ extensionAverage hbeta t stem n k x ∧
      extensionAverage hbeta t stem n k x ≤ 1 := by
  classical
  let : Nonempty (Extension stem n) := ⟨s₀⟩
  have hcard : (Fintype.card (Extension stem n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun s _ => (rootAttenuation_pow_mem_Icc hbeta t (endpoint s) x k).1)
  · have hsum : (∑ s : Extension stem n, rootAttenuation hbeta t (endpoint s) x ^ k) ≤
        (Fintype.card (Extension stem n) : ℝ) := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
        (rootAttenuation_pow_mem_Icc hbeta t (endpoint s) x k).2))
    exact (mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq (inv_mul_cancel₀ hcard)

theorem integral_root_weight_mul_pow_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (left : Bool) (v : TreeVertex d) (k : ℕ) :
    (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 *
      rootAttenuation hbeta t v (observationCopy left q) ^ k ∂copies beta μ) ≤
      ∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 ∂copies beta μ := by
  have hw := IsingCopyStationarity.integrable_fieldDifference_sq hμ hbeta t
    (ConnectedHull.root d)
  have hg := ((measurable_rootAttenuation hbeta t v).comp
    (measurable_observationCopy left)).pow_const k
  have hb (q : CopySpace d) := rootAttenuation_pow_mem_Icc hbeta t v (observationCopy left q) k
  apply integral_mono_ae (hw.mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun q => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hb q).1]
        using (hb q).2))) hw
  exact Filter.Eventually.of_forall (fun q =>
    mul_le_of_le_one_right (sq_nonneg _) (hb q).2)

theorem integral_root_weight_mul_pow_le_cut
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (left : Bool) (k : ℕ) {stem : List (Fin d)} {n : ℕ}
    (s₀ : Extension stem n) (m : ℕ)
    (F : ∀ c : TreeShell d m, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → ℝ) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d m)) (hI : I.Nonempty) {τ C : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (labelMeasure d)) ≤ τ / 4)
    (hdom : ∀ᵐ z ∂μ.prod (labelMeasure d),
      extensionAverage hbeta t stem n k (uniformObservation z) ≤
        C * ActualCutWeightedAverage.average F I z) :
    (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ k ∂copies beta μ) ≤
      (C * τ) * (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 ∂copies beta μ) +
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
          Real.exp (-(I.card : ℝ) * τ ^ 2 / 2) := by
  rw [integral_root_weight_mul_extension_average hμ hbeta t left k s₀]
  exact integral_fieldDifference_sq_mul_le hμ hbeta (ConnectedHull.root d) t left m
    F hF hbound I hI hτ hC hmean (extensionAverage hbeta t stem n k)
    (measurable_extensionAverage hbeta t stem n k)
    (extensionAverage_mem_Icc hbeta t s₀ k) hdom

end Problem367.IsingRootWeightedCut

end

end OAI
