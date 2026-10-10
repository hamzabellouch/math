import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RetainedFineDensityConfigurationMeasurable
import OAI.Analysis.CoulombRadii.FormDomain.CoreKinetic

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
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def retainedFinePower {n : ℕ} (b : ℝ) (r : Configuration n → Finset (Fin n))
    (x : Configuration n) : ℝ :=
  ∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ)

lemma retainedFinePower_nonneg {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (x : Configuration n) :
    0 ≤ retainedFinePower b r x :=
  integral_nonneg (fun _ => Real.rpow_nonneg (retainedFineDensity_nonneg ..) _)

lemma retainedFinePower_bound {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (x : Configuration n) :
    retainedFinePower b r x ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n :=
  (retainedFineDensity_power_le hb _ _).trans (fineDensityPower_bound hb _)

lemma retainedFinePower_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (retainedFinePower b r) := retainedFineDensity_power_configuration_measurable b r hr

lemma core_finePower_integrable {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => retainedFinePower b r ((joinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2) := by
  have hw : Integrable (fun z => ‖ψ.value st z‖^2) :=
    (ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)
  apply (hw.const_mul (((k:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*k)).mono'
  · exact ((retainedFinePower_measurable b r hr).comp
      (measurable_snd.comp (joinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedFinePower_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedFinePower_bound hb r _) (sq_nonneg _)

lemma retained_fine_kinetic_lower_all {n : ℕ} (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm (retainedFinePower b r) ψ -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n:ℝ)^(4/3:ℝ)) * mass ψ ≤ kinetic ψ := by
  by_cases hn : 0 < n
  · exact retained_fine_kinetic_lower hn ψ hψ hb r hr
  · have hn : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hr0 (x : Configuration 0) : r x = ∅ := Finset.eq_empty_of_forall_notMem (fun i => Fin.elim0 i)
    simpa [potentialForm, retainedFinePower, retainedFineDensity, hr0,
      Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0), Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0)]
      using (show 0 ≤ kinetic ψ from by unfold kinetic; positivity)

theorem block_retained_fine_kinetic_lower {m k : ℕ} (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins m) (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (Fin.append s t ∘ corePerm m p) (permute (corePerm m p) z) =
        (((corePerm m p).sign : ℤ) : ℂ) * ψ.value (Fin.append s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm
      (fun z => retainedFinePower b r ((joinConfiguration m k).symm z).2) ψ -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)) * mass ψ ≤ coreKinetic ψ := by
  let C := (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)
  have hs (s : Spins m) :
      thomasFermiCoefficient * (∫ x, potentialForm (retainedFinePower b r) (ψ.coreSlice s x)) -
        C * (∫ x, mass (ψ.coreSlice s x)) ≤ ∫ x, kinetic (ψ.coreSlice s x) := by
    rw [←integral_const_mul, ←integral_const_mul,
      ←integral_sub ((potentialForm_coreSlice_integrable ψ s _ (fun t => core_finePower_integrable hb r hr ψ (Fin.append s t))).const_mul _)
        ((mass_coreSlice_integrable ψ s).const_mul C)]
    apply integral_mono_ae
      (((potentialForm_coreSlice_integrable ψ s _ (fun t => core_finePower_integrable hb r hr ψ (Fin.append s t))).const_mul _).sub
        ((mass_coreSlice_integrable ψ s).const_mul C)) (kinetic_coreSlice_integrable ψ s)
    exact (ψ.coreSlice_antisymmetric s (hψ s)).mono fun x hx =>
      retained_fine_kinetic_lower_all (ψ.coreSlice s x) hx hb r hr
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hs s)
  simp only [Finset.sum_sub_distrib, ←Finset.mul_sum] at H
  rw [integral_potentialForm_coreSlice ψ _ (core_finePower_integrable hb r hr ψ),
    integral_mass_coreSlice, integral_kinetic_coreSlice] at H
  exact H

def retainedFineCoulomb {n : ℕ} (b : ℝ) (r : Configuration n → Finset (Fin n))
    (x : Configuration n) : ℝ :=
  coulombBilinear (retainedFineDensity b (r x) (position x))
    (retainedFineDensity b (r x) (position x))/2

lemma retainedFineCoulomb_nonneg {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (x : Configuration n) :
    0 ≤ retainedFineCoulomb b r x :=
  div_nonneg (retainedFineDensity_coulomb_nonneg ..) (by norm_num)

lemma retainedFineCoulomb_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (retainedFineCoulomb b r) :=
  (retainedFineDensity_coulomb_configuration_measurable b r hr).div_const 2

lemma ae_block_position_injective (m k : ℕ) :
    ∀ᵐ z : Configuration (m+k), Function.Injective (position ((joinConfiguration m k).symm z).2) := by
  filter_upwards [ae_position_injective (m+k)] with z hz
  intro i j hij
  have h : Fin.natAdd m i = Fin.natAdd m j := hz (by simpa only [position_split_right] using hij)
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

lemma ae_core_fine_pair_bound {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) :
    ∀ᵐ z : Configuration (m+k),
      retainedFineCoulomb b r ((joinConfiguration m k).symm z).2 ≤
        pairPotential ((joinConfiguration m k).symm z).2 + ((2*Real.pi+1)/(2*b))*k := by
  filter_upwards [ae_block_position_injective m k] with z hz
  have h := retained_fine_pair_lower hb (r ((joinConfiguration m k).symm z).2)
    (position ((joinConfiguration m k).symm z).2) hz
  have hc : ((r ((joinConfiguration m k).symm z).2).card : ℝ) ≤ k := by
    exact_mod_cast (show (r ((joinConfiguration m k).symm z).2).card ≤ k by simpa using Finset.card_le_univ (r ((joinConfiguration m k).symm z).2))
  have hC : 0 ≤ (2*Real.pi+1)/(2*b) := by positivity
  have hh := mul_le_mul_of_nonneg_left hc hC
  change retainedFineCoulomb b r ((joinConfiguration m k).symm z).2 -
    ((2*Real.pi+1)/(2*b))*(r ((joinConfiguration m k).symm z).2).card ≤
      pairPotential ((joinConfiguration m k).symm z).2 at h
  linarith

lemma core_fineCoulomb_integrable {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => retainedFineCoulomb b r ((joinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2) := by
  have hw : Integrable (fun z => ‖ψ.value st z‖^2) :=
    (ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)
  apply ((ψ.core_pair_integrable st).add (hw.const_mul (((2*Real.pi+1)/(2*b))*k))).mono'
  · exact ((retainedFineCoulomb_measurable b r hr).comp
      (measurable_snd.comp (joinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · filter_upwards [ae_core_fine_pair_bound (m:=m) hb r] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (retainedFineCoulomb_nonneg ..) (sq_nonneg _))]
    simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right hz (sq_nonneg ‖ψ.value st z‖)

lemma potentialForm_le_add_const {n : ℕ} (ψ : H1Vector n)
    {V W : Configuration n → ℝ} {C : ℝ}
    (hV : ∀ s, Integrable (fun x => V x*‖ψ.value s x‖^2))
    (hW : ∀ s, Integrable (fun x => W x*‖ψ.value s x‖^2))
    (h : ∀ᵐ x, V x ≤ W x+C) :
    potentialForm V ψ ≤ potentialForm W ψ + C*mass ψ := by
  have hs (s : Spins n) : (∫ x, V x*‖ψ.value s x‖^2) ≤
      (∫ x, W x*‖ψ.value s x‖^2)+C*(∫ x, ‖ψ.value s x‖^2) := by
    have hw : Integrable (fun x => ‖ψ.value s x‖^2) :=
      (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
    rw [←integral_const_mul, ←integral_add (hW s) (hw.const_mul C)]
    apply integral_mono_ae (hV s) ((hW s).add (hw.const_mul C))
    exact h.mono fun x hx => by simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right hx (sq_nonneg ‖ψ.value s x‖)
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hs s)
  simpa only [potentialForm, mass, Finset.sum_add_distrib, ←Finset.mul_sum] using H

theorem block_retained_fine_pair_lower {m k : ℕ} (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    potentialForm (fun z => retainedFineCoulomb b r ((joinConfiguration m k).symm z).2) ψ -
      (((2*Real.pi+1)/(2*b))*k)*mass ψ ≤
    potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).2) ψ :=
  sub_le_iff_le_add.mpr (potentialForm_le_add_const ψ (core_fineCoulomb_integrable hb r hr ψ)
    ψ.core_pair_integrable (ae_core_fine_pair_bound hb r))

theorem block_retained_fine_energy_lower {m k : ℕ} (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins m) (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (Fin.append s t ∘ corePerm m p) (permute (corePerm m p) z) =
        (((corePerm m p).sign : ℤ) : ℂ) * ψ.value (Fin.append s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm
      (fun z => retainedFinePower b r ((joinConfiguration m k).symm z).2) ψ +
    potentialForm (fun z => retainedFineCoulomb b r ((joinConfiguration m k).symm z).2) ψ -
      (((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)) +
        ((2*Real.pi+1)/(2*b))*k)*mass ψ ≤
      coreKinetic ψ + potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).2) ψ := by
  have h1 := block_retained_fine_kinetic_lower ψ hψ hb r hr
  have h2 := block_retained_fine_pair_lower ψ hb r hr
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
