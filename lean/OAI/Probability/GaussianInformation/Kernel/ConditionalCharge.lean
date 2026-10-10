import Mathlib
import OAI.Probability.GaussianInformation.Kernel.JointRules

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity

lemma reference_log_measurable {d N : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    Measurable (fun a : Ambient d × Fin N => Real.log (referenceWeight ν (rule.response η a.2) a.1)) := by
  apply measurable_from_prod_countable_left
  intro w
  exact (referenceWeight_measurable ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)).log

lemma reference_log_uniform_bound {d N : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,∀ s w,‖Real.log (referenceWeight ν (rule.response η w) s)‖ ≤ M := by
  classical
  have hb (w : Fin N) := referenceWeight_log_bounded hd ν hH hν _ (rule.measurable_response η w)
    rule.lower_pos (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)
  choose M hM hb using hb
  refine ⟨∑ w,M w,fun s w => (hb w s).trans ?_⟩
  exact Finset.single_le_sum (fun v _ => hM v) (Finset.mem_univ w)

lemma joint_Phi_identity {d N : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w)))=
      (InformationTheory.klDiv ν (sphereProbability d)).toReal+
        ∫ t : Ambient d × Observation (d/16) d × Fin N,
          Real.log (referenceWeight ν (rule.response η t.2.2) t.1)
          ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel := by
  obtain ⟨f,hf,hf0,hfH,hνf⟩ := bounded_density_representation (sphereProbability d) ν hH hν
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun s => ENNReal.ofReal (f s))) := hνf ▸ inferInstance
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal=∫ s,xlog (f s) ∂sphereProbability d := by
    rw [hνf,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  obtain ⟨M,hM⟩ := reference_log_uniform_bound hd ν hH hν rule hη
  have hj := joint_integral_signal ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_ne_top hη)
    (observationKernel_probability hη) rule.sum_kernel
    (fun s w => Real.log (referenceWeight ν (rule.response η w) s)) (reference_log_measurable ν rule hη) hM
  rw [hj]
  change (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w)))=
    (InformationTheory.klDiv ν (sphereProbability d)).toReal+
      ∑ w,∫ s,rule.response η w s*Real.log (referenceWeight ν (rule.response η w) s) ∂ν
  simp_rw [weighted_Phi_identity hd ν f hf hf0 hH hfH hνf _ (rule.measurable_response η _)
    rule.lower_pos (fun s => (rule.response_bounds hη _ s).1) (fun s => (rule.response_bounds hη _ s).2)]
  rw [Finset.sum_add_distrib,hD]
  congr 1
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  rw [← integral_finsetSum _ (fun w _ => hix.bdd_mul (rule.measurable_response η w).aestronglyMeasurable
    (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rule.lower_pos.le.trans (rule.response_bounds hη w s).1)]
      exact (rule.response_bounds hη w s).2)))]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← Finset.sum_mul,rule.response_sum hη,one_mul]
end KernelPotential.NoisyDrift

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere
lemma referenceWeight_pos {d N : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w) (s) :
    0 < referenceWeight ν (rule.response η w) s := by
  have := rule.post_prob hη ν w
  exact div_pos (rule.lower_pos.trans_le (rule.response_bounds hη w s).1)
    (mul_pos (rule.mass_pos hη ν w) (clippedJ_pos _ s))

lemma positive_noisy_comparison {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (hηL : η ≤ Scale.radius (DriftCutoff.level d H)) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w))) ≤
      Phi ν+10*(d:ℝ)+2*Real.log ((DriftCutoff.level d H:ℝ)+2)+
        ∫ t : Ambient d × Observation (d/16) d × Fin N,postCharge ν rule η t.2.1 t.2.2
          ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let L := DriftCutoff.level d H
  have hL : 0 < L := DriftCutoff.level_pos d H
  let q : Observation (d/16) d → ℝ := fun z =>
    PairReference.density ν (fun j : Fin L => Scale.radius j) z.1.1 z.1.2 z.2.1 z.2.2
  have hq : Measurable q := PairReference.density_measurable ν _
  have hqp (z) : 0 < q z := PairReference.density_pos hL ν _ (fun j => Scale.radius_pos j) _ _ _ _
  have hq1 : ∫⁻ z,ENNReal.ofReal (q z) ∂observationBase (d/16) d=1 := by
    unfold observationBase
    rw [lintegral_prod _ hq.ennreal_ofReal.aemeasurable]
    simp_rw [q,PairReference.density_probability hL ν _ (fun j => Scale.radius_pos j)]
    have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
    simp
  let x : Fin N → Ambient d → ℝ≥0∞ := fun w s => ENNReal.ofReal (referenceWeight ν (rule.response η w) s)
  have hx : Measurable (Function.uncurry x) := by
    apply measurable_from_prod_countable_right
    intro w
    exact (referenceWeight_measurable ν _ (rule.measurable_response η w)
      (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
      (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)).ennreal_ofReal
  have hxe (w s) : (x w s).toReal=referenceWeight ν (rule.response η w) s :=
    ENNReal.toReal_ofReal (referenceWeight_pos ν rule hη w s).le
  have hCe (z : Observation (d/16) d) (w : Fin N) : C ν (observationKernel η) x z w=
      projectedReference (post ν (rule.response η w)) η z.1.1 z.1.2 z.2.1 z.2.2 :=
    C_eq_projectedReference hd ν hHp hν _ (rule.measurable_response η w)
      (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
      (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w) η z
  have hCf (z : Observation (d/16) d) (w : Fin N) : C ν (observationKernel η) x z w ≠ ∞ := by
    rw [hCe]
    have := rule.post_prob hη ν w
    have hp := post_bounded ν hHp hν _ (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
    exact projectedReference_finite _ ((Measure.absolutelyContinuous_of_le_smul hp).ae_le
      (ae_unit_norm (by omega : 0 < d))) hη z
  have := joint_probability ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη) rule.sum_kernel
  obtain ⟨Mx,hMx⟩ := reference_log_uniform_bound hd ν hHp hν rule hη
  have hix : Integrable (fun t : Ambient d × Observation (d/16) d × Fin N => Real.log (x t.2.2 t.1).toReal)
      (joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel) := by
    simp_rw [hxe]
    refine Integrable.of_bound ((reference_log_measurable ν rule hη).comp (f := fun t : Ambient d × Observation (d/16) d × Fin N => (t.1,t.2.2))
      (measurable_fst.prodMk measurable_snd.snd)).aestronglyMeasurable Mx ?_
    exact ae_of_all _ (fun _ => hMx _ _)
  obtain ⟨Mq,_hMq,hMqb⟩ := postCharge_uniform_bound hd ν hHp hν rule hη
  have hiC : Integrable (fun t : Ambient d × Observation (d/16) d × Fin N =>
      Real.log (1+(C ν (observationKernel η) x t.2.1 t.2.2).toReal))
      (joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel) := by
    simp_rw [hCe]
    refine Integrable.of_bound ((measurable_postCharge hd ν hν rule hη).comp (f := fun t : Ambient d × Observation (d/16) d × Fin N => t.2) measurable_snd).aestronglyMeasurable Mq ?_
    exact ae_of_all _ (fun t => by change ‖postCharge ν rule η t.2.1 t.2.2‖ ≤ Mq; rw [Real.norm_eq_abs,abs_of_nonneg (hMqb _ _).1]; exact (hMqb _ _).2)
  obtain ⟨hiq,hqlo⟩ := NoisyReference.joint_reference_log hd ν hHp hν rule.kernel rule.measurable_kernel
    rule.sum_kernel L hL (DriftCutoff.reference_cut d hd hH) hη hηL
  have hqto (z) : (ENNReal.ofReal (q z)).toReal=q z := ENNReal.toReal_ofReal (hqp z).le
  have hc := log_comparison ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη) rule.sum_kernel
    x hx (fun w s => ENNReal.ofReal_pos.mpr (referenceWeight_pos ν rule hη w s))
    (fun _ _ => ENNReal.ofReal_ne_top) (fun z => ENNReal.ofReal (q z)) hq.ennreal_ofReal
    (fun z => ENNReal.ofReal_pos.mpr (hqp z)) (fun _ => ENNReal.ofReal_ne_top) hq1 hCf hix
    (by simpa only [hqto] using hiq) hiC
  simp_rw [hxe,hCe,hqto] at hc
  rw [joint_Phi_identity hd ν hHp hν rule hη]
  change (InformationTheory.klDiv ν (sphereProbability d)).toReal+_ ≤ _
  unfold Phi
  change B ν-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤ ∫ t,Real.log (q t.2.1)
    ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel at hqlo
  change _ ≤ (∫ t,postCharge ν rule η t.2.1 t.2.2 ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel)-
    ∫ t,Real.log (q t.2.1) ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel at hc
  linarith
end KernelPotential.NoisyDrift

end OAI
