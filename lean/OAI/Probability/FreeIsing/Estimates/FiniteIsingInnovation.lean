import OAI.Probability.FreeIsing.Estimates.ArrayInnovationLaw
import OAI.Probability.FreeIsing.Estimates.BoundedInnovationDrift
import OAI.Probability.FreeIsing.Estimates.FilteredFutureIndependence
import OAI.Probability.FreeIsing.Posterior.FiniteIsingFilteringRepresentation
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianHistory

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def innovation (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  plantedArrayObservation B signal v t p - nnrealTimePrimitive (mean beta D v B) t p

theorem innovation_stronglyAdapted
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    StronglyAdapted (observationFiltration B hmB D) (innovation beta D v B) :=
  (arrayNaturalFiltration_stronglyAdapted
    (fun i : D => plantedArrayObservation B signal i)
    (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t) v).sub
    (stronglyAdapted_nnrealTimePrimitive (progressive_mean beta D v B hmB hcB))

theorem continuous_innovation
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => innovation beta D v B t p) := by
  have hA := lipschitzWith_nnrealTimePrimitive_of_progressive
    (progressive_mean beta D v B hmB hcB)
    (C := 1) (fun t q => by simpa only [Real.norm_eq_abs, NNReal.coe_one] using abs_mean_le_one beta D v B t q) p
  exact ((hcB v (p.2 v)).add (NNReal.continuous_coe.mul continuous_const)).sub hA.continuous

theorem innovation_increment_drift_bound
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {s t : ℝ≥0} (hst : s ≤ t) (p : State d Ω) :
    |(innovation beta D v B t p - innovation beta D v B s p) -
      (B v t (p.2 v) - B v s (p.2 v))| ≤ 2 * ((t : ℝ) - (s : ℝ)) := by
  have hlip := innovationCorrection_two_lipschitzWith
    (progressive_mean beta D v B hmB hcB)
    (fun r q => by simpa only [Real.norm_eq_abs] using abs_mean_le_one beta D v B r q)
    (σ := fun q : State d Ω => signal q.1 v)
    (fun q => by cases hs : q.1 v <;> norm_num [signal, spinSign, hs]) p
  have h := hlip.dist_le_mul t s
  have heq : (innovation beta D v B t p - innovation beta D v B s p) -
      (B v t (p.2 v) - B v s (p.2 v)) =
      ((t : ℝ) * signal p.1 v - nnrealTimePrimitive (mean beta D v B) t p) -
      ((s : ℝ) * signal p.1 v - nnrealTimePrimitive (mean beta D v B) s p) := by
    unfold innovation plantedArrayObservation
    ring
  rw [heq]
  simpa only [Real.dist_eq, NNReal.dist_eq, NNReal.coe_ofNat,
    abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) - (s : ℝ) from sub_nonneg.mpr hst)] using h

section Posterior

variable {beta : ℝ} (D : Finset (TreeVertex d))
  (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
  (ν : TreeVertex d → Measure Ω)
  {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
  (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
  (hmB : ∀ i t, Measurable (B i t))
  (hcB : ∀ i omega, Continuous (fun t => B i t omega))
  (hposterior : ∀ v : D, ∀ t, mean beta D v B t =ᵐ[μ.prod (Measure.infinitePi ν)]
    (μ.prod (Measure.infinitePi ν))[(fun p : State d Ω => signal p.1 v) |
      observationFiltration B hmB D t])

include hB hmB hcB hposterior

theorem innovation_martingale_of_posterior (v : D) :
    Martingale (innovation beta D v B) (observationFiltration B hmB D)
      (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hs : Integrable (fun sigma => signal sigma v) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (((measurable_pi_apply (v : TreeVertex d)).comp measurable_signal).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun sigma => by
      cases hsig : sigma v <;> norm_num [signal, spinSign, hsig]
  exact compensated_observation_martingale_of_posterior_version
    (preBrownian_martingale_signalArrayFiltration μ ν hB hmB v)
    (observationFiltration_le_signal B hmB D) (hs.comp_fst _)
    (arrayNaturalFiltration_stronglyAdapted
      (fun i : D => plantedArrayObservation B signal i)
      (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t) v)
    (stronglyAdapted_mean beta D v B hmB) (hposterior v)
    (stronglyAdapted_nnrealTimePrimitive (progressive_mean beta D v B hmB hcB))
    (fun s t _ => integrable_nnreal_process_interval_of_progressive_bounded
      (progressive_mean beta D v B hmB hcB) 1
      (fun r => Filter.Eventually.of_forall (fun p => abs_mean_le_one beta D v B r p)) s t)

theorem innovation_isBrownianReal_of_posterior (v : D) :
    IsBrownianReal (innovation beta D v B) (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply BrownianInnovation.isBrownianReal_of_bounded_drift
    (planted_coordinate_preBrownian μ ν hB v)
    (innovation_martingale_of_posterior D μ ν hB hmB hcB hposterior v)
    (L := 2)
  · intro s t hst
    have h := planted_weighted_increment_sq_condExp_subfield μ ν hB hmB hst
      ({(v : TreeVertex d)} : Finset (TreeVertex d)) (fun _ => (1 : ℝ))
      (observationFiltration_le_signal B hmB D s)
    simpa only [Finset.sum_singleton, one_mul, one_pow, mul_one] using h
  · norm_num
  · intro s t hst
    exact Filter.Eventually.of_forall (innovation_increment_drift_bound beta D v B hmB hcB hst)
  · have hzero := (planted_noise_coordinate_measurePreserving μ ν v).quasiMeasurePreserving.ae
      (hB v).eval_zero_ae_eq_zero
    filter_upwards [hzero] with p hp
    simpa only [innovation, plantedArrayObservation, nnrealTimePrimitive, NNReal.coe_zero,
      zero_mul, add_zero, intervalIntegral.integral_same, sub_zero] using hp
  · exact Filter.Eventually.of_forall (continuous_innovation beta D v B hmB hcB)

theorem innovation_unit_projection_condExp_character_of_posterior
    (a : D → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    (μ.prod (Measure.infinitePi ν))[character (fun p => ∑ i : D, a i *
      (innovation beta D i B t p - innovation beta D i B s p)) u |
        observationFiltration B hmB D s] =ᵐ[μ.prod (Measure.infinitePi ν)]
      fun _ => Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  classical
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let F := observationFiltration B hmB D
  let W : ℝ≥0 → State d Ω → ℝ := fun r p => ∑ i : D, a i * innovation beta D i B r p
  let N : ℝ≥0 → State d Ω → ℝ := fun r p => ∑ i : D, a i * B i r (p.2 i)
  have hN : IsPreBrownianReal N P :=
    BrownianLinearCombination.isPreBrownianReal_sum
      (fun i : D => planted_coordinate_preBrownian μ ν hB i)
      ((planted_coordinate_paths_iIndepFun μ ν hmB).precomp Subtype.val_injective) a ha
  have hW : Martingale W F P :=
    BrownianLinearCombination.martingale_sum F
      (fun i : D => innovation_martingale_of_posterior D μ ν hB hmB hcB hposterior i) a
  let c : TreeVertex d → ℝ := fun i => if hi : i ∈ D then a ⟨i, hi⟩ else 0
  have hc (i : D) : c i = a i := by simp [c, i.property]
  have hcs : ∑ i ∈ D, c i ^ 2 = 1 := by
    rw [← Finset.sum_coe_sort D]
    simpa only [hc] using ha
  have hvariance : ∀ r v : ℝ≥0, r ≤ v →
      P[(fun p => (N v p - N r p)^2) | F r] =ᵐ[P]
        fun _ => (v : ℝ) - (r : ℝ) := by
    intro r v hrv
    have heq : (fun p : State d Ω => (N v p - N r p)^2) =
        (fun p => (∑ i ∈ D, c i * (B i v (p.2 i) - B i r (p.2 i)))^2) := by
      funext p
      rw [← Finset.sum_coe_sort D]
      simp only [hc, N, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    have h := planted_weighted_increment_sq_condExp_subfield μ ν hB hmB hrv D c
      (observationFiltration_le_signal B hmB D r)
    simpa only [hcs, mul_one] using h
  have hbound : ∀ r v : ℝ≥0, r ≤ v → ∀ᵐ p ∂P,
      |(W v p - W r p) - (N v p - N r p)| ≤
        (2 * ∑ i : D, |a i|) * ((v : ℝ) - (r : ℝ)) := by
    intro r v hrv
    apply Filter.Eventually.of_forall
    intro p
    let e : D → ℝ := fun i => (innovation beta D i B v p - innovation beta D i B r p) -
      (B i v (p.2 i) - B i r (p.2 i))
    have heq : (W v p - W r p) - (N v p - N r p) = ∑ i : D, a i * e i := by
      simp only [W, N, e, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i : D, a i * e i| ≤ ∑ i : D, |a i * e i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : D, |a i| * |e i| := by simp only [abs_mul]
      _ ≤ ∑ i : D, |a i| * (2 * ((v : ℝ) - (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (innovation_increment_drift_bound beta D i B hmB hcB hrv p) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  apply BrownianCharacterization.condExp_character_of_setIntegral (F.le s)
  · exact Finset.measurable_sum _ fun i _ =>
      ((((innovation_stronglyAdapted beta D i B hmB hcB t).mono (F.le t)).measurable).sub
        (((innovation_stronglyAdapted beta D i B hmB hcB s).mono (F.le s)).measurable)).const_mul (a i)
  · intro A hA
    have h := BrownianInnovation.setIntegral_character_of_bounded_drift hN hW hvariance
      (by positivity : 0 ≤ 2 * ∑ i : D, |a i|) hbound hst hA u
    simpa only [W, mul_sub, Finset.sum_sub_distrib] using h

theorem innovation_increment_law_and_indep_of_posterior
    {E : Type*} [mE : MeasurableSpace E] {Y : State d Ω → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[observationFiltration B hmB D s] Y) :
    HasLaw (fun p i => innovation beta D i B t p - innovation beta D i B s p)
      (Measure.pi (fun _ : D => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi ν)) ∧
    iIndepFun (fun i p => innovation beta D i B t p - innovation beta D i B s p)
      (μ.prod (Measure.infinitePi ν)) ∧
    IndepFun (fun p i => innovation beta D i B t p - innovation beta D i B s p) Y
      (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun p i => innovation beta D i B t p - innovation beta D i B s p) := by
    apply Measurable.of_eval
    intro i
    exact (((innovation_stronglyAdapted beta D i B hmB hcB t).mono
      ((observationFiltration B hmB D).le t)).measurable).sub
      (((innovation_stronglyAdapted beta D i B hmB hcB s).mono
        ((observationFiltration B hmB D).le s)).measurable)
  have h := ConditionalGaussianVector.product_gaussian_law_and_indep_of_condExp_unit_character
    ((observationFiltration B hmB D).le s) hm (t - s)
    (fun a ha u => innovation_unit_projection_condExp_character_of_posterior
      D μ ν hB hmB hcB hposterior a ha hst u) hY
  refine ⟨h.1, ?_, h.2⟩
  apply (iIndepFun_iff_hasLaw_pi_pi (fun i : D =>
    (measurePreserving_eval (fun _ : D => gaussianReal 0 (t - s)) i).fun_comp_hasLaw h.1)).mpr
  exact h.1

theorem innovation_increment_indep_filtration_of_posterior
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun p i => innovation beta D i B t p - innovation beta D i B s p) inferInstance)
      (observationFiltration B hmB D s) (μ.prod (Measure.infinitePi ν)) := by
  have h := (innovation_increment_law_and_indep_of_posterior D μ ν hB hmB hcB hposterior
    (E := State d Ω) (Y := id) (mE := observationFiltration B hmB D s)
    s t hst measurable_id).2.2
  change Indep _ ((observationFiltration B hmB D s).comap id) _ at h
  simpa only [MeasurableSpace.comap_id] using h

theorem innovation_future_indep_filtration_of_posterior (s : ℝ≥0) :
    Indep (observationFiltration B hmB D s)
      (MeasurableSpace.comap (fun p (t : Set.Ici s) i =>
        innovation beta D i B t.val p - innovation beta D i B s p) inferInstance)
      (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply FilteredFutureIndependence.indep_future
    (X := fun t p i => innovation beta D i B t p)
  · intro t
    let : MeasurableSpace (State d Ω) := observationFiltration B hmB D t
    exact Measurable.of_eval (fun i =>
      (innovation_stronglyAdapted beta D i B hmB hcB t).measurable)
  · exact innovation_increment_indep_filtration_of_posterior D μ ν hB hmB hcB hposterior

end Posterior

section Actual

variable {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
  (ν : TreeVertex d → Measure Ω)
  {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
  (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
  (hmB : ∀ i t, Measurable (B i t))
  (hcB : ∀ i omega, Continuous (fun t => B i t omega))
  (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)

include hμ hB hD

theorem mean_eq_condExp (v : D) (t : ℝ≥0) :
    mean beta D v B t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[(fun p : State d Ω => signal p.1 v) |
        observationFiltration B hmB D t] := by
  have h := hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
    (fun eta => spinSign (eta v)) t
  rw [← observationFiltration_eq_comap B hmB D t] at h
  exact h.symm

include hmB hcB

theorem innovation_martingale (v : D) :
    Martingale (innovation beta D v B) (observationFiltration B hmB D)
      (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_martingale_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) v

theorem innovation_isBrownianReal (v : D) :
    IsBrownianReal (innovation beta D v B) (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_isBrownianReal_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) v

theorem innovation_increment_law_and_indep
    {E : Type*} [MeasurableSpace E] {Y : State d Ω → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[observationFiltration B hmB D s] Y) :
    HasLaw (fun p i => innovation beta D i B t p - innovation beta D i B s p)
      (Measure.pi (fun _ : D => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi ν)) ∧
    iIndepFun (fun i p => innovation beta D i B t p - innovation beta D i B s p)
      (μ.prod (Measure.infinitePi ν)) ∧
    IndepFun (fun p i => innovation beta D i B t p - innovation beta D i B s p) Y
      (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_increment_law_and_indep_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) s t hst hY

theorem innovation_increment_indep_filtration (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun p i => innovation beta D i B t p - innovation beta D i B s p) inferInstance)
      (observationFiltration B hmB D s) (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_increment_indep_filtration_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) s t hst

theorem innovation_future_indep_filtration (s : ℝ≥0) :
    Indep (observationFiltration B hmB D s)
      (MeasurableSpace.comap (fun p (t : Set.Ici s) i =>
        innovation beta D i B t.val p - innovation beta D i B s p) inferInstance)
      (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_future_indep_filtration_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) s

end Actual
end Problem367.FiniteIsingFiltering

end

end OAI
