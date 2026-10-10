import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add
import OAI.Analysis.CoulombRadii.FieldAnalysis.RetainedFineDensity

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb
lemma retainedFineDensity_configuration_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun p : Configuration n × Space => retainedFineDensity b (r p.1) (position p.1) p.2) := by
  simp_rw [retainedFineDensity_eq_sum_ite]
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite ((hr i).preimage measurable_fst)
  · exact (fineKernel_continuous b).measurable.comp
      (measurable_snd.sub ((continuous_position i).measurable.comp measurable_fst))
  · exact measurable_const

lemma retainedFineDensity_coulomb_configuration_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun x => coulombBilinear (retainedFineDensity b (r x) (position x))
      (retainedFineDensity b (r x) (position x))) := by
  have hm := retainedFineDensity_configuration_measurable b r hr
  have hi : Measurable (fun p : Configuration n × (Space × Space) =>
      retainedFineDensity b (r p.1) (position p.1) p.2.1 *
      retainedFineDensity b (r p.1) (position p.1) p.2.2 * coulombKernel (p.2.1-p.2.2)) :=
    ((hm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).mul
        (coulombKernel_measurable.comp (by fun_prop))
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

lemma retainedFineDensity_coulomb_nonneg {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) :
    0 ≤ coulombBilinear (retainedFineDensity b r x) (retainedFineDensity b r x) :=
  integral_nonneg fun _ => mul_nonneg
    (mul_nonneg (retainedFineDensity_nonneg ..) (retainedFineDensity_nonneg ..)) (coulombKernel_nonneg _)

lemma retainedFineDensity_coulomb_weight_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector n) (s : Spins n) :
    Integrable (fun x => (coulombBilinear (retainedFineDensity b (r x) (position x))
      (retainedFineDensity b (r x) (position x))/2)*‖ψ.value s x‖^2) := by
  have hw : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
  apply ((ψ.pair_integrable s).add (hw.const_mul (((2*Real.pi+1)/(2*b))*n))).mono'
  · exact ((retainedFineDensity_coulomb_configuration_measurable b r hr).div_const 2).aestronglyMeasurable.mul
      hw.aestronglyMeasurable
  · filter_upwards [ae_retained_fine_pair_lower hb r] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (retainedFineDensity_coulomb_nonneg ..) (by norm_num)) (sq_nonneg _))]
    have hc : ((r x).card : ℝ) ≤ n := by exact_mod_cast (show (r x).card ≤ n by simpa using Finset.card_le_univ (r x))
    have hC : 0 ≤ (2*Real.pi+1)/(2*b) := by positivity
    have h := mul_le_mul_of_nonneg_left hc hC
    have H := mul_le_mul_of_nonneg_right (show coulombBilinear (retainedFineDensity b (r x) (position x))
        (retainedFineDensity b (r x) (position x))/2 ≤
        (∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (position x i-position x j) else 0) +
        ((2*Real.pi+1)/(2*b))*n by linarith) (sq_nonneg ‖ψ.value s x‖)
    simpa only [Pi.add_apply, mul_add, add_mul] using H

theorem retained_fine_pair_energy_lower {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector n) :
    (∑ s, ∫ x : Configuration n,
      (coulombBilinear (retainedFineDensity b (r x) (position x))
        (retainedFineDensity b (r x) (position x))/2)*‖ψ.value s x‖^2) -
      (((2*Real.pi+1)/(2*b))*n)*mass ψ ≤ pairEnergy ψ := by
  have hs (s : Spins n) : (∫ x : Configuration n,
      (coulombBilinear (retainedFineDensity b (r x) (position x))
        (retainedFineDensity b (r x) (position x))/2)*‖ψ.value s x‖^2) ≤
      (∫ x : Configuration n, (∑ i : Fin n, ∑ j : Fin n,
        if i < j then coulombKernel (position x i-position x j) else 0)*‖ψ.value s x‖^2) +
      (((2*Real.pi+1)/(2*b))*n)*(∫ x, ‖ψ.value s x‖^2) := by
    have hw : Integrable (fun x => ‖ψ.value s x‖^2) :=
      (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
    rw [←integral_const_mul, ←integral_add (ψ.pair_integrable s) (hw.const_mul _)]
    apply integral_mono_ae (retainedFineDensity_coulomb_weight_integrable hb r hr ψ s)
      ((ψ.pair_integrable s).add (hw.const_mul _))
    filter_upwards [ae_retained_fine_pair_lower hb r] with x hx
    have hc : ((r x).card : ℝ) ≤ n := by exact_mod_cast (show (r x).card ≤ n by simpa using Finset.card_le_univ (r x))
    have hC : 0 ≤ (2*Real.pi+1)/(2*b) := by positivity
    have h := mul_le_mul_of_nonneg_left hc hC
    have H := mul_le_mul_of_nonneg_right (show coulombBilinear (retainedFineDensity b (r x) (position x))
        (retainedFineDensity b (r x) (position x))/2 ≤
        (∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (position x i-position x j) else 0) +
        ((2*Real.pi+1)/(2*b))*n by linarith) (sq_nonneg ‖ψ.value s x‖)
    simpa only [Pi.add_apply, mul_add, add_mul] using H
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hs s)
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum] at H
  exact sub_le_iff_le_add.mpr H

theorem retained_fine_energy_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * (∑ s, ∫ x : Configuration n,
      (∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ))*‖ψ.value s x‖^2) +
    (∑ s, ∫ x : Configuration n,
      (coulombBilinear (retainedFineDensity b (r x) (position x))
        (retainedFineDensity b (r x) (position x))/2)*‖ψ.value s x‖^2) -
      (((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n:ℝ)^(4/3:ℝ)) +
        ((2*Real.pi+1)/(2*b))*n) * mass ψ ≤ kinetic ψ + pairEnergy ψ := by
  have h1 := retained_fine_kinetic_lower hn ψ hψ hb r hr
  have h2 := retained_fine_pair_energy_lower hb r hr ψ
  linarith
end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal

end

end OAI
