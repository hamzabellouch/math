import OAI.Probability.FreeIsing.Ising.CopyOrbitAverage
import OAI.Probability.FreeIsing.Ising.CopyWeightedCut
import OAI.Probability.FreeIsing.Trees.InfiniteCanonicalPathResponse
import OAI.Probability.FreeIsing.Trees.PathPrefix

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootAttenuation

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingCopyOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def rootAttenuation (hbeta : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d)
    (x : Paths d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (fun w => field beta w t x) (ConnectedHull.takeVertex v (i + 1))
        (ConnectedHull.takeVertex v i))

theorem rootResponseProduct_eq (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (x : Paths d) :
    CavityFieldLimit.rootResponseProduct hbeta v (fun i => x i t) =
      Real.tanh beta ^ v.1.length * rootAttenuation hbeta t v x := rfl

theorem measurable_rootAttenuation (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) : Measurable (rootAttenuation hbeta t v) := by
  unfold rootAttenuation
  apply Finset.measurable_prod
  intro i hi
  apply (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
  exact (CavityArray.measurable_field_apply (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta) (ConnectedHull.takeVertex v (i + 1))
      (ConnectedHull.takeVertex v i)).comp
        (Measurable.of_eval (fun w =>
          (measurable_field_joint beta w).comp (measurable_const.prodMk measurable_id)))

theorem rootAttenuation_mem_Icc (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (x : Paths d) :
    0 ≤ rootAttenuation hbeta t v x ∧ rootAttenuation hbeta t v x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg fun i _ =>
      (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
  · exact Finset.prod_le_one₀
      (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)

omit [IsProbabilityMeasure μ] in
theorem rootAttenuation_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun x => rootAttenuation hbeta t v (relabel g.symm x)) =ᵐ[observationLaw μ]
      rootAttenuation hbeta t (g.toEquiv v) := by
  filter_upwards [IsingCopyStationarity.field_array_relabel_ae hμ g.symm t] with x hx
  unfold rootAttenuation
  rw [g.length_eq_of_root_eq hg v]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hx, CavityArray.field_relabel]
  change responseAttenuation (Real.tanh beta)
      (CavityArray.field _ _ (fun w => field beta w t x)
        (g.toEquiv (ConnectedHull.takeVertex v (i + 1)))
        (g.toEquiv (ConnectedHull.takeVertex v i))) = _
  rw [g.map_takeVertex_of_root_eq hg, g.map_takeVertex_of_root_eq hg]

theorem rootAttenuation_pow_mem_Icc (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (x : Paths d) (k : ℕ) :
    0 ≤ rootAttenuation hbeta t v x ^ k ∧ rootAttenuation hbeta t v x ^ k ≤ 1 :=
  ⟨pow_nonneg (rootAttenuation_mem_Icc hbeta t v x).1 _,
    pow_le_one₀ (rootAttenuation_mem_Icc hbeta t v x).1
      (rootAttenuation_mem_Icc hbeta t v x).2⟩

theorem integral_root_weight_mul_extension_average
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (left : Bool) (k : ℕ) {stem : List (Fin d)} {n : ℕ}
    (s₀ : Extension stem n) :
    (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ k ∂copies beta μ) =
      ∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 *
        WeightedOrbitAverage.average (fun s : Extension stem n => fun q =>
          rootAttenuation hbeta t (endpoint s) (observationCopy left q) ^ k) q
        ∂copies beta μ := by
  apply integral_fieldDifference_sq_mul_extension_average hμ hbeta t
    (ConnectedHull.root d) (Nat.zero_le _) s₀
    (fun v q => rootAttenuation hbeta t v (observationCopy left q) ^ k)
  · intro v
    exact ((measurable_rootAttenuation hbeta t v).comp
      (measurable_observationCopy left)).pow_const k
  · intro v q
    exact rootAttenuation_pow_mem_Icc hbeta t v (observationCopy left q) k
  · intro g hg v
    have hr : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d :=
      hg (ConnectedHull.root d) (Nat.zero_le _)
    have h := (measurePreserving_observationCopy (beta := beta) (μ := μ) left).quasiMeasurePreserving.ae
      (rootAttenuation_relabel_ae hμ hbeta g hr t v)
    filter_upwards [h] with q hq
    have hobs : observationCopy left (copyAction g q) =
        relabel g.symm (observationCopy left q) := by cases left <;> rfl
    rw [hobs, hq]

end Problem367.IsingRootAttenuation

end

end OAI
