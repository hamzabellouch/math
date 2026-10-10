import Mathlib
import OAI.Analysis.CoulombRadii.Localization.TruncatedCoulomb

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
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma density_memLp_fiveThirds (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (ht : Integrable (fun x => ρ x^(5/3:ℝ))) : MemLp ρ (5/3:ℝ≥0∞) := by
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num : (5/3:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ℝ≥0∞) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (hp _)] using ht

lemma compact_density_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (K : Set Space) (hK : IsCompact K)
    (hs : ∀ x, x ∉ K → ρ x = 0) : Integrable ρ := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hLp : MemLp ρ (5/3:ℝ≥0∞) (volume.restrict K) :=
    (density_memLp_fiveThirds ρ hp hm ht).mono_measure Measure.restrict_le_self
  have hI := hLp.integrable (by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num : (1:ℝ≥0∞) ≤ 5/3)
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero hI hs

noncomputable def nearCoulombFiveHalves (x : Space) : ℝ :=
  (Metric.ball (0:Space) 1).indicator (fun y => coulombKernel y^(5/2:ℝ)) x

lemma nearCoulombFiveHalves_integrable : Integrable nearCoulombFiveHalves := by
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 5/2) (by simp [Space]) (by norm_num [Space])
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (coulombKernel_nonneg x) _),one_mul]
    change (‖x‖⁻¹)^(5/2:ℝ) ≤ ‖x‖^(-(5/2:ℝ))
    rw [Real.inv_rpow (norm_nonneg x),Real.rpow_neg (norm_nonneg x)]
  · exact (coulombKernel_measurable.pow_const _).aestronglyMeasurable

lemma nearCoulombFiveHalves_nonneg (x : Space) : 0 ≤ nearCoulombFiveHalves x :=
  Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (coulombKernel_nonneg y) _) x

lemma density_coulomb_integrand_bound (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (x y : Space) :
    coulombKernel (x-y)*ρ y ≤ nearCoulombFiveHalves (x-y) + ρ y^(5/3:ℝ) + ρ y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) 1
  · rw [nearCoulombFiveHalves,Set.indicator_of_mem h]
    have HY := Real.young_inequality_of_nonneg (coulombKernel_nonneg (x-y)) (hp y)
      (show (5/2:ℝ).HolderConjugate (5/3:ℝ) from ⟨by norm_num,by norm_num,by norm_num⟩)
    have H1 := Real.rpow_nonneg (coulombKernel_nonneg (x-y)) (5/2:ℝ)
    have H2 := Real.rpow_nonneg (hp y) (5/3:ℝ)
    linarith [hp y]
  · rw [nearCoulombFiveHalves,Set.indicator_of_notMem h,zero_add]
    have hn : (1:ℝ) ≤ ‖x-y‖ := by simpa [Metric.mem_ball,dist_zero_right] using h
    have hk : coulombKernel (x-y) ≤ 1 := by simpa [coulombKernel] using inv_anti₀ (by norm_num : (0:ℝ)<1) hn
    have H := mul_le_mul_of_nonneg_right hk (hp y)
    linarith [Real.rpow_nonneg (hp y) (5/3:ℝ)]

lemma density_coulomb_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) := by
  apply (((nearCoulombFiveHalves_integrable.comp_sub_left x).add ht).add hi).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖coulombKernel (x-y)*ρ y‖ ≤ nearCoulombFiveHalves (x-y) + ρ y^(5/3:ℝ) + ρ y
  rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hp y))]
  exact density_coulomb_integrand_bound ρ hp x y

lemma density_coulomb_bound (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (x : Space) :
    (∫ y, coulombKernel (x-y)*ρ y) ≤
      (∫ y, nearCoulombFiveHalves y) + (∫ y, ρ y^(5/3:ℝ)) + ∫ y, ρ y := by
  calc
    _ ≤ ∫ y, nearCoulombFiveHalves (x-y) + ρ y^(5/3:ℝ) + ρ y :=
      integral_mono (density_coulomb_integrable ρ hp hm hi ht x)
        (((nearCoulombFiveHalves_integrable.comp_sub_left x).add ht).add hi)
        (density_coulomb_integrand_bound ρ hp x)
    _ = _ := by
      have HA := integral_add ((nearCoulombFiveHalves_integrable.comp_sub_left x).add ht) hi
      have HB := integral_add (nearCoulombFiveHalves_integrable.comp_sub_left x) ht
      simp only [Pi.add_apply] at HA HB
      rw [HA,HB,integral_sub_left_eq_self]

lemma density_coulomb_pair_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (ht : Integrable (fun x => ρ x^(5/3:ℝ))) :
    Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) := by
  have hm' : Measurable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) :=
    (coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((hm.comp measurable_fst).mul (hm.comp measurable_snd))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with x
    apply ((density_coulomb_integrable ρ hp hm hi ht x).const_mul (ρ x)).congr
    filter_upwards [] with y
    ring
  · let C := (∫ y, nearCoulombFiveHalves y) + (∫ y, ρ y^(5/3:ℝ)) + ∫ y, ρ y
    apply (hi.mul_const C).mono' hm'.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    have he : (∫ y, ‖coulombKernel (x-y)*(ρ x*ρ y)‖) =
        ρ x*(∫ y, coulombKernel (x-y)*ρ y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hp _) (hp _)))]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (density_coulomb_bound ρ hp hm hi ht x) (hp x)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
