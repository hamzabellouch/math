import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshThermalLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {A S E : Type*} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace E]
variable (κ : Kernel A S) [IsMarkovKernel κ]
variable (P : Measure A) [IsProbabilityMeasure P] (G : Measure E) [IsProbabilityMeasure G]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))
variable (F : E→S→ℝ) (hF : Measurable (Function.uncurry F))
variable (f : ℝ →ᵇ ℝ) (hFb : ∀ g x, |F g x|≤‖f‖)

def boundedThermalPartition (a : A×E) : ℝ :=
  tiltMean (κ a.1) (H a.1) (fun x => Real.exp (F a.2 x)) 1

include hH hF in
lemma boundedThermalPartition_measurable : Measurable (boundedThermalPartition κ H F) := by
  let κ' : Kernel (A×E) S := κ.comap Prod.fst measurable_fst
  exact kernel_tiltMean_measurable κ'
    (hH.comp (measurable_fst.fst.prodMk measurable_snd))
    ((hF.comp (measurable_fst.snd.prodMk measurable_snd)).exp)

include hH hF hFb in
lemma boundedThermalPartition_mem {a : A}
    (he : Integrable (fun x => Real.exp (H a x)) (κ a)) (g : E) :
    boundedThermalPartition κ H F (a,g)∈FreshPartitionRange f := by
  have he1 : Integrable (fun x => Real.exp (1*H a x)) (κ a) := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable (κ a) he1
  let μ := tiltLaw (κ a) (H a) 1
  have hi : Integrable (fun x => Real.exp (F g x)) μ := by
    apply Integrable.of_bound hF.of_uncurry_left.exp.aestronglyMeasurable (Real.exp ‖f‖)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (abs_le.mp (hFb g x)).2
  unfold boundedThermalPartition
  rw [← tilt_law_integral_of_integrable (κ a) hH.of_uncurry_left he1]
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-‖f‖))) hi
        (fun x => Real.exp_le_exp.mpr (abs_le.mp (hFb g x)).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hi (integrable_const (Real.exp ‖f‖))
        (fun x => Real.exp_le_exp.mpr (abs_le.mp (hFb g x)).2)

def boundedThermalLaw : ProbabilityMeasure (FreshPartitionRange f) :=
  ⟨(P.prod G).map (fun a => freshPartitionClip f (boundedThermalPartition κ H F a)),
    (Measure.isProbabilityMeasure_map_iff ((freshPartitionClip_measurable f).comp
      (boundedThermalPartition_measurable κ H hH F hF)).aemeasurable).2 inferInstance⟩

include hFb in
lemma boundedThermalLaw_integral
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a))
    (J : ℝ→ℝ) (hJ : Measurable J) :
    (∫ x, J x.val ∂(boundedThermalLaw κ P G H hH F hF f : Measure (FreshPartitionRange f)))=
      ∫ a, J (boundedThermalPartition κ H F a) ∂P.prod G := by
  change (∫ x : FreshPartitionRange f, J x.val ∂(P.prod G).map
    (fun a => freshPartitionClip f (boundedThermalPartition κ H F a)))=_
  have hm := integral_map (μ := P.prod G) (f := fun x : FreshPartitionRange f => J x.val)
    (φ := fun a => freshPartitionClip f (boundedThermalPartition κ H F a))
    (((freshPartitionClip_measurable f).comp
      (boundedThermalPartition_measurable κ H hH F hF)).aemeasurable)
    ((hJ.comp measurable_subtype_coe).aestronglyMeasurable)
  refine hm.trans ?_
  apply integral_congr_ae
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae he] with a ha
  rw [freshPartitionClip_eq f (boundedThermalPartition_mem κ H hH F hF f hFb ha a.2)]

include hH hF hFb in
lemma boundedThermalPartition_power_integrable (r : ℕ) :
    Integrable (fun a => boundedThermalPartition κ H F a^r) (P.prod G) := by
  apply Integrable.of_bound ((boundedThermalPartition_measurable κ H hH F hF).pow_const r).aestronglyMeasurable
    ((Real.exp ‖f‖)^r)
  apply ae_of_all
  intro a
  rw [norm_pow,Real.norm_eq_abs]
  apply pow_le_pow_left₀ (abs_nonneg _)
  apply tiltMean_bound_general (κ a.1) hH.of_uncurry_left hF.of_uncurry_left.exp (Real.exp_pos _).le
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (abs_le.mp (hFb a.2 x)).2

include hFb in
lemma boundedThermalLaw_moment
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) :
    (∫ x, x.val^r ∂(boundedThermalLaw κ P G H hH F hF f : Measure (FreshPartitionRange f)))=
      ∫ a, ∫ g, (tiltMean (κ a) (H a) (fun x => Real.exp (F g x)) 1)^r ∂G ∂P := by
  rw [boundedThermalLaw_integral κ P G H hH F hF f hFb he (fun x => x^r) (by fun_prop),
    integral_prod _ (boundedThermalPartition_power_integrable κ P G H hH F hF f hFb r)]
  rfl

include hH hF hFb in
lemma boundedThermalPartition_log_bound (a : A×E) :
    |Real.log (boundedThermalPartition κ H F a)|≤‖f‖ :=
  log_tiltMean_exp_bound_general (κ a.1) hH.of_uncurry_left hF.of_uncurry_left (norm_nonneg _)
    (hFb a.2)

include hH hF hFb in
lemma boundedThermalPartition_log_integrable :
    Integrable (fun a => Real.log (boundedThermalPartition κ H F a)) (P.prod G) := by
  apply Integrable.of_bound
    ((boundedThermalPartition_measurable κ H hH F hF).log).aestronglyMeasurable ‖f‖
  exact ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs] using boundedThermalPartition_log_bound κ H hH F hF f hFb a

include hFb in
lemma boundedThermalLaw_log
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    (∫ x, Real.log x.val ∂(boundedThermalLaw κ P G H hH F hF f : Measure (FreshPartitionRange f)))=
      ∫ a, ∫ g, Real.log (tiltMean (κ a) (H a) (fun x => Real.exp (F g x)) 1) ∂G ∂P := by
  rw [boundedThermalLaw_integral κ P G H hH F hF f hFb he _ Real.measurable_log,
    integral_prod _ (boundedThermalPartition_log_integrable κ P G H hH F hF f hFb)]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
