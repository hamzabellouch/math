import Mathlib
import OAI.Probability.Perceptron.Interpolation.IntegrableReplicaGibbs
import OAI.Probability.Perceptron.Variational.UnboundedContact

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

abbrev FreshPartitionRange (f : ℝ →ᵇ ℝ) := Icc (Real.exp (-‖f‖)) (Real.exp ‖f‖)

private lemma freshPartition_lower_le_upper (f : ℝ →ᵇ ℝ) : Real.exp (-‖f‖)≤Real.exp ‖f‖ :=
  Real.exp_le_exp.mpr (neg_le_self (norm_nonneg f))

def freshPartitionClip (f : ℝ →ᵇ ℝ) (x : ℝ) : FreshPartitionRange f :=
  ⟨max (Real.exp (-‖f‖)) (min (Real.exp ‖f‖) x),le_max_left _ _,
    max_le (freshPartition_lower_le_upper f) (min_le_left _ _)⟩

lemma freshPartitionClip_measurable (f : ℝ →ᵇ ℝ) : Measurable (freshPartitionClip f) := by
  apply Measurable.subtype_mk
  exact measurable_const.max (measurable_const.min measurable_id)

lemma freshPartitionClip_eq (f : ℝ →ᵇ ℝ) {x : ℝ} (hx : x∈FreshPartitionRange f) :
    (freshPartitionClip f x).val=x := by
  dsimp [freshPartitionClip]
  rw [min_eq_right hx.2,max_eq_right hx.1]

variable {A S E : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))
variable (v : S→E) (hv : Measurable v) (f : ℝ →ᵇ ℝ)

def freshThermalPartition (a : A×E) : ℝ :=
  tiltMean (κ a.1) (H a.1) (fun x => Real.exp (f (inner ℝ (v x) a.2))) 1

include hH hv in
lemma freshThermalPartition_measurable : Measurable (freshThermalPartition κ H v f) := by
  let κ' : Kernel (A×E) S := κ.comap (fun a : A×E => a.1) measurable_fst
  have hH' : Measurable (fun a : (A×E)×S => H a.1.1 a.2) :=
    hH.comp (measurable_fst.fst.prodMk measurable_snd)
  have hF : Measurable (fun a : (A×E)×S => Real.exp (f (inner ℝ (v a.2) a.1.2))) :=
    (f.measurable.comp ((hv.comp measurable_snd).inner measurable_fst.snd)).exp
  exact kernel_tiltMean_measurable κ' hH' hF

include hH hv in
lemma freshThermalPartition_mem {a : A}
    (he : Integrable (fun x => Real.exp (H a x)) (κ a)) (g : E) :
    freshThermalPartition κ H v f (a,g)∈FreshPartitionRange f := by
  have he1 : Integrable (fun x => Real.exp (1*H a x)) (κ a) := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable (κ a) he1
  let μ := tiltLaw (κ a) (H a) 1
  have hm : Measurable (fun x => Real.exp (f (inner ℝ (v x) g))) :=
    (f.measurable.comp (hv.inner measurable_const)).exp
  have hi : Integrable (fun x => Real.exp (f (inner ℝ (v x) g))) μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp ‖f‖)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm _))
  have hb x := abs_le.mp (f.norm_coe_le_norm (inner ℝ (v x) g))
  unfold freshThermalPartition
  rw [← tilt_law_integral_of_integrable (κ a) hH.of_uncurry_left he1]
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-‖f‖))) hi (fun x => Real.exp_le_exp.mpr (hb x).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hi (integrable_const (Real.exp ‖f‖)) (fun x => Real.exp_le_exp.mpr (hb x).2)

def freshThermalLaw : ProbabilityMeasure (FreshPartitionRange f) :=
  ⟨(P.prod (stdGaussian E)).map (fun a => freshPartitionClip f (freshThermalPartition κ H v f a)), by
    exact (Measure.isProbabilityMeasure_map_iff ((freshPartitionClip_measurable f).comp
      (freshThermalPartition_measurable κ H hH v hv f)).aemeasurable).2 inferInstance⟩

lemma freshThermalLaw_integral (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a))
    (F : ℝ→ℝ) (hF : Measurable F) :
    (∫ x, F x.val ∂(freshThermalLaw κ P H hH v hv f : Measure (FreshPartitionRange f)))=
      ∫ a, F (freshThermalPartition κ H v f a) ∂P.prod (stdGaussian E) := by
  change (∫ x : FreshPartitionRange f, F x.val ∂(P.prod (stdGaussian E)).map
    (fun a => freshPartitionClip f (freshThermalPartition κ H v f a)))=_
  have hmap := integral_map (μ := P.prod (stdGaussian E))
    (f := fun x : FreshPartitionRange f => F x.val)
    (φ := fun a => freshPartitionClip f (freshThermalPartition κ H v f a))
    (((freshPartitionClip_measurable f).comp
      (freshThermalPartition_measurable κ H hH v hv f)).aemeasurable)
    ((hF.comp measurable_subtype_coe).aestronglyMeasurable)
  refine hmap.trans ?_
  apply integral_congr_ae
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae he] with a ha
  rw [freshPartitionClip_eq f (freshThermalPartition_mem κ H hH v hv f ha a.2)]

include hH hv in
lemma freshThermalPartition_power_integrable (r : ℕ) :
    Integrable (fun a => freshThermalPartition κ H v f a^r) (P.prod (stdGaussian E)) := by
  apply Integrable.of_bound ((freshThermalPartition_measurable κ H hH v hv f).pow_const r).aestronglyMeasurable
    ((Real.exp ‖f‖)^r)
  apply ae_of_all
  intro a
  rw [norm_pow,Real.norm_eq_abs]
  apply pow_le_pow_left₀ (abs_nonneg _)
  apply tiltMean_bound_general (κ a.1) hH.of_uncurry_left
    ((f.measurable.comp (hv.inner measurable_const)).exp) (Real.exp_pos _).le
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((abs_le.mp (f.norm_coe_le_norm _)).2)

lemma freshThermalLaw_moment (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) :
    (∫ x, x.val^r ∂(freshThermalLaw κ P H hH v hv f : Measure (FreshPartitionRange f)))=
      ∫ a, ∫ g, (tiltMean (κ a) (H a) (fun x => expBCF 1 f (inner ℝ (v x) g)) 1)^r
        ∂stdGaussian E ∂P := by
  rw [freshThermalLaw_integral κ P H hH v hv f he (fun x => x^r) (by fun_prop),
    integral_prod _ (freshThermalPartition_power_integrable κ P H hH v hv f r)]
  simp only [freshThermalPartition,expBCF_apply,one_mul]

include hH hv in
lemma freshThermalPartition_log_integrable
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    Integrable (fun a => Real.log (freshThermalPartition κ H v f a)) (P.prod (stdGaussian E)) := by
  apply Integrable.of_bound
    ((freshThermalPartition_measurable κ H hH v hv f).log).aestronglyMeasurable ‖f‖
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae he] with a ha
  have hb := freshThermalPartition_mem κ H hH v hv f ha a.2
  have hpos : 0<freshThermalPartition κ H v f a := (Real.exp_pos _).trans_le hb.1
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hb.1
  · simpa only [Real.log_exp] using Real.log_le_log hpos hb.2

lemma freshThermalLaw_log (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    (∫ x, Real.log x.val ∂(freshThermalLaw κ P H hH v hv f : Measure (FreshPartitionRange f)))=
      ∫ a, ∫ g, Real.log (tiltMean (κ a) (H a)
        (fun x => Real.exp (f (inner ℝ (v x) g))) 1) ∂stdGaussian E ∂P := by
  rw [freshThermalLaw_integral κ P H hH v hv f he _ Real.measurable_log,
    integral_prod _ (freshThermalPartition_log_integrable κ P H hH v hv f he)]
  rfl

end

lemma log_tiltMean_exp_bound_general {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H F : S→ℝ}
    (hH : Measurable H) (hF : Measurable F) {C : ℝ} (hC : 0≤C)
    (hFC : ∀ x, |F x|≤C) :
    |Real.log (tiltMean μ H (fun x => Real.exp (F x)) 1)|≤C := by
  by_cases hi : Integrable (fun x => Real.exp (1*H x)) μ
  · let := tilt_law_probability_of_integrable μ hi
    let ν := tiltLaw μ H 1
    have hf : Integrable (fun x => Real.exp (F x)) ν := by
      apply Integrable.of_bound hF.exp.aestronglyMeasurable (Real.exp C)
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (abs_le.mp (hFC x)).2
    have hlo : Real.exp (-C)≤∫ x, Real.exp (F x) ∂ν := by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
        integral_mono (integrable_const (Real.exp (-C))) hf
          (fun x => Real.exp_le_exp.mpr (abs_le.mp (hFC x)).1)
    have hhi : (∫ x, Real.exp (F x) ∂ν)≤Real.exp C := by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
        integral_mono hf (integrable_const (Real.exp C))
          (fun x => Real.exp_le_exp.mpr (abs_le.mp (hFC x)).2)
    have hp := (Real.exp_pos (-C)).trans_le hlo
    rw [← tilt_law_integral_of_integrable μ hH hi]
    apply abs_le.mpr
    constructor
    · exact (Real.log_exp (-C)).symm.trans_le (Real.log_le_log (Real.exp_pos _) hlo)
    · exact (Real.log_le_log hp hhi).trans_eq (Real.log_exp C)
  · simp only [tiltMean,tiltPartition,integral_undef hi,div_zero,Real.log_zero,abs_zero]
    exact hC

end SphericalPerceptronFreeEnergy
end

end OAI
