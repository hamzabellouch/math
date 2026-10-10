import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.SmoothCompact
import OAI.Analysis.CoulombRadii.FieldAnalysis.PairRegroup

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
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
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
lemma coulombKernel_integrableOn_ball (R : ℝ) : IntegrableOn coulombKernel (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact Filter.Eventually.of_forall (fun x => by simp [coulombKernel, Real.rpow_neg_one])
  · exact coulombKernel_measurable.aestronglyMeasurable

lemma coulombKernel_ball_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space in Metric.ball 0 R, coulombKernel x) = 2 * Real.pi * R^2 := by
  have H := integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t < R then t⁻¹ else 0)
  have hleft : (∫ x : Space in Metric.ball 0 R, coulombKernel x) =
      ∫ x : Space, (if ‖x‖ < R then ‖x‖⁻¹ else 0) := by
    rw [← integral_indicator measurableSet_ball]
    simp only [Set.indicator, Metric.mem_ball, dist_zero_right, coulombKernel]
  rw [hleft, H]
  have hball : volume.real (Metric.ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [hdim, hball, nsmul_eq_mul, smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ), t^(3-1) * (if t < R then t⁻¹ else 0)) = ∫ t in Ioo 0 R, t := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Iio R).indicator (fun u : ℝ => u) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        by_cases h : t < R
        · simp only [h, ite_true, Set.indicator, mem_Iio]
          norm_num
          field_simp
        · simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  rw [hint, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR]
  norm_num [integral_id]
  ring

noncomputable def truncatedCoulomb (R : ℝ) (x : Space) : ℝ :=
  (Metric.ball (0:Space) R).indicator coulombKernel x
lemma truncatedCoulomb_nonneg (R : ℝ) (x : Space) : 0 ≤ truncatedCoulomb R x :=
  Set.indicator_nonneg (fun _ _ => coulombKernel_nonneg _) x
lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) :=
  (coulombKernel_integrableOn_ball R).integrable_indicator measurableSet_ball
lemma truncatedCoulomb_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, truncatedCoulomb R x) = 2*Real.pi*R^2 := by
  unfold truncatedCoulomb
  rw [integral_indicator measurableSet_ball, coulombKernel_ball_integral hR]

lemma coulomb_integrand_bound {f : Space → ℝ} {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) * f y ≤ M * truncatedCoulomb R (x-y) + R⁻¹ * f y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    have H := mul_le_mul_of_nonneg_left (hfM y) (coulombKernel_nonneg (x-y))
    linarith [mul_nonneg (inv_nonneg.mpr hR.le) (hf0 y)]
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, mul_zero, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hR hn) (hf0 y)

lemma coulomb_convolution_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    Integrable (fun y => coulombKernel (x-y) * f y) := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  apply ((hnear.const_mul M).add (hf.const_mul R⁻¹)).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y) * f y‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hf0 _))]
    exact coulomb_integrand_bound hf0 hfM hR x y)

lemma coulomb_convolution_bound {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {M R : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfM : ∀ y, f y ≤ M) (hR : 0 < R) (x : Space) :
    (∫ y, coulombKernel (x-y) * f y) ≤ 2*Real.pi*M*R^2 + R⁻¹ * ∫ y, f y := by
  have hnear := (truncatedCoulomb_integrable R).comp_sub_left x
  calc
    _ ≤ ∫ y, M * truncatedCoulomb R (x-y) + R⁻¹ * f y :=
      integral_mono (coulomb_convolution_integrable hf hm hf0 hfM hR x)
        ((hnear.const_mul M).add (hf.const_mul R⁻¹)) (coulomb_integrand_bound hf0 hfM hR x)
    _ = _ := by
      rw [integral_add (hnear.const_mul M) (hf.const_mul R⁻¹), integral_const_mul,
        integral_const_mul, integral_sub_left_eq_self, truncatedCoulomb_integral hR.le]
      ring

lemma coulomb_signed_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have h := coulomb_convolution_integrable hf.norm hm.norm (fun y => norm_nonneg _) hM
    (by norm_num : (0:ℝ) < 1) x
  apply h.mono' (((coulombKernel_measurable.comp (by fun_prop)).mul hm).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖coulombKernel (x-y)*f y‖ ≤ coulombKernel (x-y)*‖f y‖
    rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)] )

lemma coulomb_pair_integrable {f g : Space → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hg : Integrable g) (hgm : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) := by
  have hm : Measurable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul (coulombKernel_measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    have hi := (coulomb_signed_convolution_integrable hg hgm hM x).const_mul (f x)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)
  · let A : ℝ := 2*Real.pi*M + ∫ y, ‖g y‖
    have hb (x : Space) : (∫ y, coulombKernel (x-y)*‖g y‖) ≤ A := by
      simpa [A] using coulomb_convolution_bound hg.norm hgm.norm (fun y => norm_nonneg _) hM
        (by norm_num : (0:ℝ) < 1) x
    have he (x : Space) :
        (∫ y, ‖f x*g y*coulombKernel (x-y)‖) = ‖f x‖*(∫ y, coulombKernel (x-y)*‖g y‖) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
      simp_rw [mul_assoc, mul_comm ‖g _‖ (coulombKernel _)]
      rw [integral_const_mul]
    apply (hf.norm.mul_const A).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun x => by
      change ‖∫ y, ‖f x*g y*coulombKernel (x-y)‖‖ ≤ ‖f x‖*A
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
      exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))

lemma compact_coulomb_cross_integrable (f g u v : Space → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hu : Continuous u) (hv : Continuous v)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun xy : Space × Space => (coulombKernel (xy.1-xy.2) : ℂ) *
      ((star (f xy.1)*u xy.1)*(star (g xy.2)*v xy.2))) := by
  have hF : Continuous (fun x => ‖f x‖*‖u x‖) := hf.norm.mul hu.norm
  have hG : Continuous (fun x => ‖g x‖*‖v x‖) := hg.norm.mul hv.norm
  have hFC : HasCompactSupport (fun x => ‖f x‖*‖u x‖) := hfc.norm.mul_right
  have hGC : HasCompactSupport (fun x => ‖g x‖*‖v x‖) := hgc.norm.mul_right
  obtain ⟨M,hM⟩ := hGC.exists_bound_of_continuous hG
  have H := coulomb_pair_integrable (hF.integrable_of_hasCompactSupport hFC) hF.measurable
    (hG.integrable_of_hasCompactSupport hGC) hG.measurable hM
  apply H.mono' ?_ (ae_of_all _ (fun xy => ?_))
  · exact (((coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).complex_ofReal).mul
      (((hf.star.mul hu).measurable.comp measurable_fst).mul
      ((hg.star.mul hv).measurable.comp measurable_snd))).aestronglyMeasurable
  · simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (coulombKernel_nonneg _)]
    exact le_of_eq (by ring)

lemma flatSpinOrbital_coulomb_cross_integrable {ι : Type*} [Fintype ι] (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) (a b c d : ι) :
    Integrable (fun xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)) =>
      (coulombKernel (WithLp.toLp 2 xy.1.2 - WithLp.toLp 2 xy.2.2) : ℂ) *
      ((star (flatSpinOrbital (v a) xy.1)*flatSpinOrbital (v c) xy.1)*
        (star (flatSpinOrbital (v b) xy.2)*flatSpinOrbital (v d) xy.2)))
      (spinSpaceMeasure.prod spinSpaceMeasure) := by
  have hsp (s t : Fin 2) := compact_coulomb_cross_integrable
    (fun x => v a x s) (fun x => v b x t) (fun x => v c x s) (fun x => v d x t)
    (hv a s).continuous (hv b t).continuous (hv c s).continuous (hv d t).continuous
    (hC a s) (hC b t)
  have hm0 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  have hm := hm0.prod hm0
  let F (sz : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : ℂ :=
    (coulombKernel (WithLp.toLp 2 sz.2.1 - WithLp.toLp 2 sz.2.2) : ℂ) *
      ((star (v a (WithLp.toLp 2 sz.2.1) sz.1.1)*v c (WithLp.toLp 2 sz.2.1) sz.1.1)*
      (star (v b (WithLp.toLp 2 sz.2.2) sz.1.2)*v d (WithLp.toLp 2 sz.2.2) sz.1.2))
  have hF : Integrable F (Measure.count.prod (volume.prod volume)) :=
    integrable_finite_count_prod F (fun st => hm.integrable_comp_of_integrable (hsp st.1 st.2))
  have hR := pairRegroup_measurePreserving (Measure.count : Measure (Fin 2))
    (volume : Measure (Fin 3 → ℝ)) (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [count_prod_count] at hR
  exact hR.integrable_comp_of_integrable hF
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
