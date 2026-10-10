import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

noncomputable section

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
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb

lemma volume_real_ball_three (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure Space).real (ball 0 r) = 4*Real.pi/3*r^3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring

lemma integral_ball_norm_sq_three (r : ℝ) (hr : 0 ≤ r) :
    (∫ p : Space in ball 0 r, ‖p‖^2) = 4*Real.pi/5*r^5 := by
  have he : (fun p : Space => (ball 0 r).indicator (fun p => ‖p‖^2) p) =
      fun p : Space => (Iio r).indicator (fun t : ℝ => t^2) ‖p‖ := by
    ext p
    simp only [Set.indicator, mem_ball, dist_zero_right, mem_Iio]
  rw [← integral_indicator measurableSet_ball, he,
    integral_fun_norm_addHaar volume]
  simp only [Space, finrank_euclideanSpace_fin, Nat.reduceSub,
    nsmul_eq_mul, smul_eq_mul]
  have hf : (fun t : ℝ => t^2 * (Iio r).indicator (fun s : ℝ => s^2) t) =
      (Iio r).indicator (fun t : ℝ => t^4) := by
    ext t
    by_cases ht : t < r <;> simp [Set.indicator, ht]
    ring
  rw [hf, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by ext t; simp; tauto
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
    integral_pow, volume_real_ball_three 1 (by norm_num)]
  norm_num
  ring

lemma integrableOn_ball_norm_sq_three (r : ℝ) :
    IntegrableOn (fun p : Space => ‖p‖^2) (ball 0 r) := by
  exact (continuous_norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Space) r) |>.mono_set ball_subset_closedBall

noncomputable def phaseRegion (R : Space → ℝ) : Set (Space × Space) :=
  {yp | ‖yp.2‖ < R yp.1}
noncomputable def phaseMeasure (R : Space → ℝ) : Measure (Space × Space) :=
  (volume.prod volume).restrict (phaseRegion R)
lemma phaseRegion_measurable {R : Space → ℝ} (hR : Measurable R) :
    MeasurableSet (phaseRegion R) := by
  exact measurableSet_lt measurable_snd.norm (hR.comp measurable_fst)
lemma phaseMeasure_le (R : Space → ℝ) : phaseMeasure R ≤ volume.prod volume :=
  Measure.restrict_le_self

lemma phaseMeasure_lintegral {R : Space → ℝ} (hR : Measurable R)
    (f : Space × Space → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ yp, f yp ∂phaseMeasure R) = ∫⁻ y : Space, ∫⁻ p in ball 0 (R y), f (y,p) := by
  rw [phaseMeasure, ← lintegral_indicator (phaseRegion_measurable hR),
    lintegral_prod _ (hf.indicator (phaseRegion_measurable hR)).aemeasurable]
  apply lintegral_congr
  intro y
  rw [← lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro p
  by_cases hnorm : ‖p‖ < R y <;> simp [phaseRegion, Set.indicator, hnorm]

lemma phaseMeasure_mass {R : Space → ℝ} (hR : Measurable R) :
    phaseMeasure R univ = ∫⁻ y : Space,
      ENNReal.ofReal (R y)^3 * ENNReal.ofReal (Real.pi*4/3) := by
  rw [← lintegral_one, phaseMeasure_lintegral hR _ measurable_const]
  simp

lemma phaseMeasure_lintegral_momentum {R : Space → ℝ} (hR : Measurable R)
    (hRp : ∀ y, 0 ≤ R y) :
    (∫⁻ yp, ENNReal.ofReal (‖yp.2‖^2) ∂phaseMeasure R) =
      ∫⁻ y : Space, ENNReal.ofReal (4*Real.pi/5*R y^5) := by
  rw [phaseMeasure_lintegral hR _ (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_ball_norm_sq_three (R y))
    (Filter.Eventually.of_forall (fun p => sq_nonneg _)), integral_ball_norm_sq_three _ (hRp y)]

lemma phaseMeasure_momentum_memLp {R : Space → ℝ} (hR : Measurable R)
    (hRp : ∀ y, 0 ≤ R y) (hI : Integrable (fun y => R y^5)) :
    MemLp (fun yp : Space × Space => yp.2) 2 (phaseMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun yp => sq_nonneg _)),
    phaseMeasure_lintegral_momentum hR hRp,
    ← ofReal_integral_eq_lintegral_ofReal (hI.const_mul (4*Real.pi/5))
      (Filter.Eventually.of_forall (fun y => mul_nonneg (by positivity) (pow_nonneg (hRp y) _)))]
  exact ENNReal.ofReal_lt_top

lemma phaseMeasure_real_momentum {R : Space → ℝ} (hR : Measurable R)
    (hRp : ∀ y, 0 ≤ R y) :
    (∫ yp, ‖yp.2‖^2 ∂phaseMeasure R) = 4*Real.pi/5 * ∫ y : Space, R y^5 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun yp => sq_nonneg _))
    (by fun_prop), phaseMeasure_lintegral_momentum hR hRp,
    ← integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => mul_nonneg (by positivity) (pow_nonneg (hRp y) _))) (by fun_prop), integral_const_mul]

noncomputable def fermiRadius (ρ : Space → ℝ) (y : Space) : ℝ :=
  (3/(8*Real.pi)*ρ y) ^ (1/3 : ℝ)
lemma fermiRadius_nonneg (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    0 ≤ fermiRadius ρ y := Real.rpow_nonneg (mul_nonneg (by positivity) (hρ y)) _
lemma fermiRadius_cube (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    fermiRadius ρ y ^ 3 = 3/(8*Real.pi)*ρ y := by
  rw [fermiRadius, ← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ y))]
  norm_num
lemma fermiRadius_fifth (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    fermiRadius ρ y ^ 5 = (3/(8*Real.pi))^(5/3 : ℝ) * ρ y^(5/3 : ℝ) := by
  rw [fermiRadius, ← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ y)), Real.mul_rpow (by positivity) (hρ y)]
  norm_num
lemma fermiRadius_measurable (ρ : Space → ℝ) (hρ : Measurable ρ) :
    Measurable (fermiRadius ρ) := by
  unfold fermiRadius
  fun_prop
lemma fermiRadius_ball_mass (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    (volume : Measure Space) (ball 0 (fermiRadius ρ y)) = ENNReal.ofReal (ρ y/2) := by
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (fermiRadius_nonneg ρ hρ y),
    ← ENNReal.ofReal_mul (pow_nonneg (fermiRadius_nonneg ρ hρ y) _), fermiRadius_cube ρ hρ y]
  congr 1
  field_simp
  ring

lemma fermiMeasure_mass (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (hI : Integrable ρ) :
    phaseMeasure (fermiRadius ρ) univ = ENNReal.ofReal ((∫ y : Space, ρ y)/2) := by
  rw [← lintegral_one, phaseMeasure_lintegral (fermiRadius_measurable ρ hm) _ measurable_const]
  simp only [lintegral_one, Measure.restrict_apply_univ, fermiRadius_ball_mass ρ hρ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.div_const 2)
    (Filter.Eventually.of_forall (fun y => div_nonneg (hρ y) (by norm_num))), integral_div]

lemma fermiMeasure_finite (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (hI : Integrable ρ) : IsFiniteMeasure (phaseMeasure (fermiRadius ρ)) := by
  constructor
  rw [fermiMeasure_mass ρ hρ hm hI]
  exact ENNReal.ofReal_lt_top

lemma fermiMeasure_momentum_memLp (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hI : Integrable (fun y => ρ y^(5/3 : ℝ))) :
    MemLp (fun yp : Space × Space => yp.2) 2 (phaseMeasure (fermiRadius ρ)) := by
  apply phaseMeasure_momentum_memLp (fermiRadius_measurable ρ hm) (fermiRadius_nonneg ρ hρ)
  simp only [fermiRadius_fifth ρ hρ]
  exact hI.const_mul _
end Coulomb

end

end OAI
