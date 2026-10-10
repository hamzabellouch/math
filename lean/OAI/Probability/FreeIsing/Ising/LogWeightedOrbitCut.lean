import OAI.Probability.FreeIsing.Ising.CopyPathWeightNaturality
import OAI.Probability.FreeIsing.Ising.CopyWeightedPathCut
import OAI.Probability.FreeIsing.Ising.RootWeightedCut

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal BigOperators

namespace Problem367.IsingLogWeightedOrbitCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open IsingCopyPathBounds IsingCopyWeightedCut IsingCopyOrbitAverage
open IsingRootAttenuation IsingRootWeightedCut TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem pathLogDifference_sq_copyAction_invariant {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    {stem : List (Fin d)}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length)
    (g : TreeAut d) (hg : FixesStemBall stem g) :
    ∀ᵐ q ∂copies beta μ,
      pathLogDifference hbeta t s e (copyAction g q) ^ 2 =
        pathLogDifference hbeta t s e q ^ 2 := by
  have hfix (v : TreeVertex d) (hv : v.1.length ≤ stem.length) :
      g.symm.toEquiv v = v := by
    change g.toEquiv.symm v = v
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hg v hv]
  exact pathLogDifference_sq_relabel_eq_ae hμ hbeta g.symm t s e
    (fun i hi => ⟨hfix _ (hstem i hi).1, hfix _ (hstem i hi).2⟩)

theorem integral_path_weight_mul_extension_average {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (left : Bool) (k : ℕ) {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n) :
    (∫ q, pathLogDifference hbeta t s e q ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ k ∂copies beta μ) =
      ∫ q, pathLogDifference hbeta t s e q ^ 2 *
        extensionAverage hbeta t stem n k (observationCopy left q) ∂copies beta μ := by
  apply TreeOrbitAverage.integral_weight_mul_extension_average s₀ copyAction
    (measurePreserving_copyAction hμ) (fun q => pathLogDifference hbeta t s e q ^ 2)
    (fun v q => rootAttenuation hbeta t v (observationCopy left q) ^ k)
    (pathLogDifference_sq_copyAction_invariant hμ hbeta t s e hstem)
  · intro g hg v
    have hr : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d :=
      hg (ConnectedHull.root d) (Nat.zero_le _)
    have h := (measurePreserving_observationCopy (beta := beta) (μ := μ) left).quasiMeasurePreserving.ae
      (rootAttenuation_relabel_ae hμ hbeta g hr t v)
    filter_upwards [h] with q hq
    have hobs : observationCopy left (copyAction g q) =
        relabel g.symm (observationCopy left q) := by cases left <;> rfl
    rw [hobs, hq]
  · apply (integrable_pathLogDifference_sq hμ hbeta t s e).mul_bdd
      (((measurable_rootAttenuation hbeta t (endpoint s₀)).comp
        (measurable_observationCopy left)).pow_const k).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg
        (rootAttenuation_pow_mem_Icc hbeta t (endpoint s₀) (observationCopy left q) k).1]
        using (rootAttenuation_pow_mem_Icc hbeta t (endpoint s₀) (observationCopy left q) k).2)

theorem integral_path_weight_mul_pow_le {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (left : Bool) (v : TreeVertex d) (k : ℕ) :
    (∫ q, pathLogDifference hbeta t s e q ^ 2 *
      rootAttenuation hbeta t v (observationCopy left q) ^ k ∂copies beta μ) ≤
      ∫ q, pathLogDifference hbeta t s e q ^ 2 ∂copies beta μ := by
  have hw := integrable_pathLogDifference_sq hμ hbeta t s e
  have hg := ((measurable_rootAttenuation hbeta t v).comp
    (measurable_observationCopy left)).pow_const k
  have hb (q : CopySpace d) := rootAttenuation_pow_mem_Icc hbeta t v (observationCopy left q) k
  apply integral_mono_ae (hw.mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun q => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hb q).1]
        using (hb q).2))) hw
  exact Filter.Eventually.of_forall (fun q =>
    mul_le_of_le_one_right (sq_nonneg _) (hb q).2)

theorem integral_path_weight_mul_pow_le_cut {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) (left : Bool) (k : ℕ)
    {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n) (m : ℕ)
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
    (∫ q, pathLogDifference hbeta t s e q ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ k ∂copies beta μ) ≤
      (C * τ) * (∫ q, pathLogDifference hbeta t s e q ^ 2 ∂copies beta μ) +
        ((s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) *
          Real.exp (-(I.card : ℝ) * τ ^ 2 / 2) := by
  rw [integral_path_weight_mul_extension_average hμ hbeta t s e left k hstem s₀]
  exact IsingCopyWeightedPathCut.integral_pathLogDifference_sq_mul_le hμ hbeta ht s e left m
    F hF hbound I hI hτ hC hmean (extensionAverage hbeta t stem n k)
    (measurable_extensionAverage hbeta t stem n k)
    (extensionAverage_mem_Icc hbeta t s₀ k) hdom

end Problem367.IsingLogWeightedOrbitCut

end

end OAI
