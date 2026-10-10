import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfFunctionalGapControl

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
noncomputable def tfPotential (f : TFLp (volume.restrict Ω)) (x : Space) : ℝ :=
  ∫ y, coulombKernel (x-y)*tfExtend Ω f y
include hΩ
lemma tfPotential_integrand (f : TFLp (volume.restrict Ω)) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*tfExtend Ω f y) :=
  coulomb_lp_convolution_integrable (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f)
    (tfExtend_memLp hΩ f) x
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_measurable (f : TFLp (volume.restrict Ω)) : Measurable (tfPotential f) := by
  have H : StronglyMeasurable (fun p : Space × Space => coulombKernel (p.1-p.2)*tfExtend Ω f p.2) :=
    ((coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((tfExtend_measurable hΩ f).comp measurable_snd)).stronglyMeasurable
  exact H.integral_prod_right'.measurable
lemma tfPotential_bound (f : TFLp (volume.restrict Ω)) (x : Space) :
    ‖tfPotential f x‖ ≤ ((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ))*‖f‖ := by
  calc
    _ ≤ ∫ y, ‖coulombKernel (x-y)*tfExtend Ω f y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, coulombKernel (x-y)*‖tfExtend Ω f y‖ := by
      simp only [norm_mul,Real.norm_of_nonneg (coulombKernel_nonneg _)]
    _ ≤ _ := tfExtend_convolution_bound hΩ f x
lemma tfPotential_memLp (f : TFLp (volume.restrict Ω)) :
    MemLp (tfPotential f) TFFieldExponent (volume.restrict Ω) :=
  MemLp.of_bound (tfPotential_measurable hΩ f).aestronglyMeasurable _
    (Eventually.of_forall (tfPotential_bound hΩ f))
noncomputable def tfPotentialField (f : TFLp (volume.restrict Ω)) : TFLq (volume.restrict Ω) :=
  (tfPotential_memLp hΩ f).toLp (tfPotential f)
lemma tfPotentialField_coe (f : TFLp (volume.restrict Ω)) :
    tfPotentialField hΩ f =ᵐ[volume.restrict Ω] tfPotential f := MemLp.coeFn_toLp _
lemma tfCoulomb_eq_potential (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f g = ∫ x in Ω, f x*tfPotential g x := by
  rw [tfCoulomb,Measure.volume_eq_prod,integral_prod _ (tfCoulomb_integrable hΩ f g)]
  rw [← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show (∫ y, tfExtend Ω f x*tfExtend Ω g y*coulombKernel (x-y)) =
      tfExtend Ω f x*tfPotential g x by
    unfold tfPotential
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring]
  by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]
lemma tfCoulomb_eq_field (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f g = tfFieldContinuous (tfPotentialField hΩ g) f := by
  rw [tfCoulomb_eq_potential hΩ,tfFieldContinuous_apply]
  apply integral_congr_ae
  filter_upwards [tfPotentialField_coe hΩ g] with x hx
  rw [hx,mul_comm]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
noncomputable def tfIndicator (s : Set α) (hs : MeasurableSet s) : TFLp μ :=
  ((memLp_const (p := TFExponent) (μ := μ) (1:ℝ)).indicator hs).toLp (s.indicator (fun _ => 1))
lemma tfIndicator_coe (s : Set α) (hs : MeasurableSet s) :
    (tfIndicator s hs : TFLp μ) =ᵐ[μ] s.indicator (fun _ => 1) := MemLp.coeFn_toLp _
lemma tfIndicator_nonneg (s : Set α) (hs : MeasurableSet s) : TFNonneg (tfIndicator s hs : TFLp μ) := by
  filter_upwards [tfIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
lemma tfIndicator_bound (s : Set α) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, |(tfIndicator s hs : TFLp μ) x| ≤ 1 := by
  filter_upwards [tfIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]
lemma tfField_indicator (W : TFLq μ) (s : Set α) (hs : MeasurableSet s) :
    tfFieldContinuous W (tfIndicator s hs) = ∫ x in s, W x ∂μ := by
  rw [tfFieldContinuous_apply,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [tfIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]
lemma tfDual_nonneg (W : TFLq μ)
    (hW : ∀ h : TFLp μ, TFNonneg h → (∀ᵐ x ∂μ, |h x| ≤ 1) → 0 ≤ tfFieldContinuous W h) :
    ∀ᵐ x ∂μ, 0 ≤ W x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp W).integrable (by norm_num [TFFieldExponent]))
  intro s hs _
  rw [←tfField_indicator W s hs]
  exact hW _ (tfIndicator_nonneg s hs) (tfIndicator_bound s hs)
omit [IsFiniteMeasure μ] in
lemma tfKineticField_memLp (f : TFLp μ) :
    MemLp (fun x => ‖f x‖^(2/3:ℝ)) TFFieldExponent μ := by
  have H := (Lp.memLp f).norm_rpow_div (ENNReal.ofReal (2/3:ℝ))
  have he : TFExponent / ENNReal.ofReal (2/3:ℝ) = TFFieldExponent := by
    rw [TFExponent,TFFieldExponent,←ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2/3)]
    norm_num
  rw [he] at H
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤2/3)] at H
  exact H
noncomputable def tfKineticField (f : TFLp μ) : TFLq μ :=
  (tfKineticField_memLp f).toLp (fun x => ‖f x‖^(2/3:ℝ))
omit [IsFiniteMeasure μ] in
lemma tfKineticField_coe (f : TFLp μ) :
    tfKineticField f =ᵐ[μ] (fun x => ‖f x‖^(2/3:ℝ)) := MemLp.coeFn_toLp _
omit [IsFiniteMeasure μ] in
lemma tfKineticField_pair {f : TFLp μ} (hf : TFNonneg f) (h : TFLp μ) :
    tfFieldContinuous (tfKineticField f) h = ∫ x, (f x)^(2/3:ℝ)*h x ∂μ := by
  rw [tfFieldContinuous_apply]
  apply integral_congr_ae
  filter_upwards [tfKineticField_coe f,hf] with x hx hy
  rw [hx,Real.norm_of_nonneg hy]
omit [IsFiniteMeasure μ] in
lemma tfKineticField_self {f : TFLp μ} (hf : TFNonneg f) :
    tfFieldContinuous (tfKineticField f) f = ‖f‖^(5/3:ℝ) := by
  rw [tfKineticField_pair hf,←tfLp_nonneg_power hf]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  have H := Real.rpow_add_one' hx (by norm_num : (2/3:ℝ)+1≠0)
  norm_num at H
  exact H.symm
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
lemma tfPower_hasDerivAt {f h : α → ℝ} (hf : MemLp f TFExponent μ)
    (hh : AEStronglyMeasurable h μ) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) :
    HasDerivAt (fun t : ℝ => ∫ x, (f x+t*h x)^(5/3:ℝ) ∂μ)
      ((5/3:ℝ)*(∫ x, (f x)^(2/3:ℝ)*h x ∂μ)) 0 := by
  let F : ℝ → α → ℝ := fun t x => (f x+t*h x)^(5/3:ℝ)
  let F' : ℝ → α → ℝ := fun t x => (5/3:ℝ)*(f x+t*h x)^(2/3:ℝ)*h x
  let b : α → ℝ := fun x => (5/3:ℝ)*(|f x|+1)
  have hfi : Integrable f μ := hf.integrable (by norm_num [TFExponent])
  have hbi : Integrable b μ := (hfi.abs.add (integrable_const 1)).const_mul _
  have hFm : ∀ t, AEStronglyMeasurable (F t) μ := fun t => ((hf.aestronglyMeasurable.add (hh.const_mul t)).aemeasurable.pow_const _).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (F' 0) μ := by
    dsimp only [F']
    exact ((((hf.aestronglyMeasurable.add (hh.const_mul 0)).aemeasurable.pow_const _).aestronglyMeasurable).const_mul _).mul hh
  have hF0 : Integrable (F 0) μ := by
    have H := hf.integrable_norm_rpow (by norm_num [TFExponent]) (by simp)
    have H' : Integrable (fun x => |f x|^(5/3:ℝ)) μ := by
      norm_num [TFExponent] at H
      exact H
    refine H'.mono' (hFm 0) ?_
    filter_upwards [] with x
    simpa [F,Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (f x) (5/3:ℝ)
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0:ℝ) 1, ‖F' t x‖ ≤ b x := by
    filter_upwards [hb] with x hx t ht
    have ht1 : |t| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using ht)
    have hv : |f x+t*h x| ≤ |f x|+1 :=
      (abs_add_le _ _).trans (by rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg (h x)])
    have hp : |(f x+t*h x)^(2/3:ℝ)| ≤ |f x|+1 :=
      (Real.abs_rpow_le_abs_rpow _ _).trans
        ((Real.rpow_le_rpow (abs_nonneg _) hv (by norm_num)).trans
          (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg (f x)]) (by norm_num)))
    dsimp [F',b]
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<5/3)]
    calc
      _ ≤ (5/3:ℝ)*(|f x|+1)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hp (by norm_num)) hx (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0:ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x t _
    have H := ((hasDerivAt_const t (f x)).add ((hasDerivAt_id t).mul_const (h x))).rpow_const
      (p := (5/3:ℝ)) (Or.inr (by norm_num))
    convert H using 1 <;> norm_num [F,F',mul_comm,mul_left_comm]
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall hFm) hF0 hF'm hbound hbi hdiff
  simpa only [F,F',zero_mul,add_zero,mul_assoc,integral_const_mul] using H.2
lemma nonneg_deriv_of_min_on_right {F : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt F d 0)
    (hm : ∀ t : ℝ, 0 ≤ t → F 0 ≤ F t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [mem_Ioi] at ht
  simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using div_nonneg (sub_nonneg.mpr (hm t ht.le)) ht.le
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
