import OAI.Probability.FreeIsing.Ising.OrientedPath

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingCopyPathBounds IsingCopyWeightedCut
open IsingCopyOrbitAverage IsingLogWeightedOrbitCut TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edge_map (inward : Bool) (v : TreeVertex d) (i : ℕ)
    (g : TreeAut d) (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d) :
    edge inward (g.toEquiv v) i =
      (g.toEquiv (edge inward v i).1, g.toEquiv (edge inward v i).2) := by
  cases inward <;> simp only [edge, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [g.map_takeVertex_of_root_eq hg, g.map_takeVertex_of_root_eq hg]

omit [IsProbabilityMeasure μ] in
theorem attenuation_relabel_ae [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (g : TreeAut d) (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    (fun x => attenuation hb t inward v (relabel g.symm x)) =ᵐ[observationLaw μ]
      attenuation hb t inward (g.toEquiv v) := by
  have he (i : ℕ) := cavityObservable_relabel_ae hμ hb g.symm t
    (edge inward v i).1 (edge inward v i).2
  filter_upwards [ae_all_iff.mpr he] with x hx
  unfold attenuation
  rw [g.length_eq_of_root_eq hg v]
  apply Finset.prod_congr rfl
  intro i hi
  rw [edge_map inward v i g hg]
  exact congrArg (responseAttenuation (Real.tanh beta)) (hx i)

def extensionAverage (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (stem : List (Fin d)) (n : ℕ) : Paths d → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun x =>
    attenuation hb t inward (endpoint s) x ^ 2)

theorem measurable_extensionAverage (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (stem : List (Fin d)) (n : ℕ) :
    Measurable (extensionAverage hb t inward stem n) := by
  unfold extensionAverage WeightedOrbitAverage.average
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun s _ =>
    (measurable_attenuation hb t inward (endpoint s)).pow_const 2)

theorem extensionAverage_mem_Icc (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) {stem : List (Fin d)} {n : ℕ}
    (s₀ : Extension stem n) (x : Paths d) :
    0 ≤ extensionAverage hb t inward stem n x ∧
      extensionAverage hb t inward stem n x ≤ 1 := by
  classical
  let : Nonempty (Extension stem n) := ⟨s₀⟩
  have hcard : (Fintype.card (Extension stem n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbnd (s : Extension stem n) : attenuation hb t inward (endpoint s) x ^ 2 ≤ 1 :=
    pow_le_one₀ (attenuation_mem_Icc hb t inward (endpoint s) x).1
      (attenuation_mem_Icc hb t inward (endpoint s) x).2
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun s _ => sq_nonneg _)
  · have hs : (∑ s : Extension stem n, attenuation hb t inward (endpoint s) x ^ 2) ≤
        (Fintype.card (Extension stem n) : ℝ) := by
      simpa using (Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbnd s))
    exact (mul_le_mul_of_nonneg_left hs
      (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq (inv_mul_cancel₀ hcard)

theorem integral_log_weight_mul_extension_average {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (left inward : Bool) {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n) :
    (∫ q, pathLogDifference hb t s e q ^ 2 *
      attenuation hb t inward (endpoint s₀) (observationCopy left q) ^ 2 ∂copies beta μ) =
      ∫ q, pathLogDifference hb t s e q ^ 2 *
        extensionAverage hb t inward stem n (observationCopy left q) ∂copies beta μ := by
  apply TreeOrbitAverage.integral_weight_mul_extension_average s₀ copyAction
    (measurePreserving_copyAction hμ) (fun q => pathLogDifference hb t s e q ^ 2)
    (fun v q => attenuation hb t inward v (observationCopy left q) ^ 2)
    (pathLogDifference_sq_copyAction_invariant hμ hb t s e hstem)
  · intro g hg v
    have hr : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d :=
      hg (ConnectedHull.root d) (Nat.zero_le _)
    have h := (measurePreserving_observationCopy (beta := beta) (μ := μ) left).quasiMeasurePreserving.ae
      (attenuation_relabel_ae hμ hb g hr t inward v)
    filter_upwards [h] with q hq
    have hobs : observationCopy left (copyAction g q) =
        relabel g.symm (observationCopy left q) := by cases left <;> rfl
    rw [hobs, hq]
  · apply (integrable_pathLogDifference_sq hμ hb t s e).mul_bdd
      (((measurable_attenuation hb t inward (endpoint s₀)).comp
        (measurable_observationCopy left)).pow_const 2).aestronglyMeasurable
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (attenuation_mem_Icc hb t inward _ _).1
      (attenuation_mem_Icc hb t inward _ _).2

theorem integral_log_weight_mul_le_of_tail {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) (left inward : Bool)
    {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (htail : (observationLaw μ)
      {x | a < extensionAverage hb t inward stem n x} ≤ ENNReal.ofReal ε) :
    (∫ q, pathLogDifference hb t s e q ^ 2 *
      attenuation hb t inward (endpoint s₀) (observationCopy left q) ^ 2 ∂copies beta μ) ≤
      a * (∫ q, pathLogDifference hb t s e q ^ 2 ∂copies beta μ) +
        ((s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) * ε := by
  rw [integral_log_weight_mul_extension_average hμ hb t s e left inward hstem s₀]
  have hprob : (copies beta μ)
      {q | a < extensionAverage hb t inward stem n (observationCopy left q)} ≤
        ENNReal.ofReal ε := by
    have hp := (measurePreserving_observationCopy (beta := beta) (μ := μ) left).measure_preimage
      ((measurable_extensionAverage hb t inward stem n) (measurableSet_Ioi (a := a))).nullMeasurableSet
    exact hp.trans_le htail
  exact DependentWeight.integral_mul_le_of_tail_probability
    (integrable_pathLogDifference_sq hμ hb t s e)
    ((measurable_extensionAverage hb t inward stem n).comp (measurable_observationCopy left))
    ha (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Filter.Eventually.of_forall fun q => sq_nonneg _)
    (ae_pathLogDifference_sq_bound hμ hb ht s e)
    (Filter.Eventually.of_forall fun q => (extensionAverage_mem_Icc hb t inward s₀ _).1)
    (Filter.Eventually.of_forall fun q => (extensionAverage_mem_Icc hb t inward s₀ _).2)
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq (ENNReal.toReal_ofReal hε))

end Problem367.IsingOrientedPath

end

end OAI
