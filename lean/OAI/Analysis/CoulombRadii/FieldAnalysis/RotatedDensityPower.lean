import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Pullback
import OAI.Analysis.CoulombRadii.Localization.ConfigSupported
import OAI.Analysis.CoulombRadii.FieldAnalysis.CommonIsometryApply
import OAI.Analysis.CoulombRadii.FieldAnalysis.Rotation

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
namespace Coulomb

lemma flat_fine_density_kinetic_lower_euclidean {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : Configuration n, flatDensityPower b x.ofLp * ‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  have H := flat_fine_density_kinetic_lower hn ψ hψ hb
  convert H using 1
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n × Fin 3)).integral_comp'
    (fun x => flatDensityPower b x * ‖ψ.value s (WithLp.toLp 2 x)‖^2)

lemma commonIsometry_symm {n : ℕ} (L : Space ≃ₗᵢ[ℝ] Space) :
    (commonIsometry (n:=n) L).symm = commonIsometry L.symm := by
  ext x ij
  rfl

lemma fixed_rotation_fine_density_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) (Q : Rotation) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : Configuration n,
        (∫ y : Space, rotatedFlatDensity b Q (position x) y^(5/3:ℝ)) * ‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  let L := commonIsometry (n:=n) (rotationIsometry Q)
  have has : Antisymmetric (ψ.pullback L.symm) := by
    rw [show L.symm = commonIsometry (rotationIsometry Q).symm from commonIsometry_symm _]
    exact hψ.pullback_common _
  have H := flat_fine_density_kinetic_lower_euclidean hn (ψ.pullback L.symm) has hb
  rw [mass_pullback, kinetic_pullback] at H
  convert H using 1
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  have hp := (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp'
      (fun x : Configuration n => flatDensityPower b x.ofLp * ‖ψ.value s (L.symm x)‖^2)
  change (∫ x : Configuration n, flatDensityPower b (L x).ofLp * ‖ψ.value s (L.symm (L x))‖^2) = _ at hp
  simpa only [H1Vector.pullback, rotatedFlatDensityPower_eq, LinearIsometryEquiv.symm_apply_apply] using hp

noncomputable def rotatedDensityPower {n : ℕ} (b : ℝ) (Q : Rotation) (x : Configuration n) : ℝ :=
  ∫ y : Space, rotatedFlatDensity b Q (position x) y^(5/3:ℝ)

lemma rotatedDensityPower_nonneg {n : ℕ} (b : ℝ) (Q : Rotation) (x : Configuration n) :
    0 ≤ rotatedDensityPower b Q x :=
  integral_nonneg (fun _ => Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)
lemma rotatedDensityPower_le {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Configuration n) :
    rotatedDensityPower b Q x ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n :=
  rotatedFlatDensity_power_integral_le hb ..

lemma rotation_configuration_continuous {n : ℕ} :
    Continuous (fun p : Rotation × Configuration n => commonIsometry (rotationIsometry p.1) p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  have hs : Continuous (fun p : Rotation × Configuration n => (p.1, position p.2 ij.1)) :=
    continuous_fst.prodMk ((continuous_position ij.1).comp continuous_snd)
  have hc := rotation_action_continuous.comp hs
  have H := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) ij.2).comp hc
  exact H

lemma rotatedDensityPower_measurable {n : ℕ} (b : ℝ) :
    Measurable (fun p : Rotation × Configuration n => rotatedDensityPower b p.1 p.2) := by
  simp_rw [rotatedDensityPower, rotatedFlatDensityPower_eq]
  exact (flatDensityPower_measurable b).comp
    ((PiLp.continuous_ofLp 2 _).measurable.comp rotation_configuration_continuous.measurable)

lemma fineDensityPower_configuration_measurable {n : ℕ} (b : ℝ) :
    Measurable (fun x : Configuration n => fineDensityPower b (position x)) := by
  have hm : Measurable (fun p : Configuration n × Space =>
      fineDensity b (position p.1) p.2^(5/3:ℝ)) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    exact (fineKernel_measurable b).comp
      (measurable_snd.sub ((continuous_position i).measurable.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma fineDensityPower_nonneg {n : ℕ} (b : ℝ) (x : Fin n → Space) :
    0 ≤ fineDensityPower b x :=
  integral_nonneg (fun _ => Real.rpow_nonneg (fineDensity_nonneg ..) _)

lemma fineDensityPower_bound {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    fineDensityPower b x ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n := by
  apply (fineDensityPower_le_angularAverage hb x).trans
  calc
    _ ≤ ∫ _ : Rotation, ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n ∂rotationMeasure :=
      integral_mono (rotatedFlatDensity_power_integrable_prod hb x).integral_prod_left
        (integrable_const _) (fun Q => rotatedFlatDensity_power_integral_le hb Q x)
    _ = _ := by simp

lemma weighted_rotatedDensityPower_integrable_prod {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun p : Rotation × Configuration n => rotatedDensityPower b p.1 p.2 * w p.2)
      (rotationMeasure.prod volume) := by
  apply ((hw.const_mul (((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n)).comp_snd rotationMeasure).mono'
    ((rotatedDensityPower_measurable b).aestronglyMeasurable.mul (hw.comp_snd rotationMeasure).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖rotatedDensityPower b p.1 p.2 * w p.2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (rotatedDensityPower_nonneg ..) (hw0 _))]
    exact mul_le_mul_of_nonneg_right (rotatedDensityPower_le hb ..) (hw0 _))

lemma weighted_fineDensityPower_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun x => fineDensityPower b (position x) * w x) := by
  apply (hw.const_mul (((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n)).mono'
    ((fineDensityPower_configuration_measurable b).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖fineDensityPower b (position x) * w x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (fineDensityPower_nonneg ..) (hw0 _))]
    exact mul_le_mul_of_nonneg_right (fineDensityPower_bound hb ..) (hw0 _))

lemma weighted_fineDensityPower_le_angular {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, fineDensityPower b (position x) * w x) ≤
      ∫ Q, (∫ x, rotatedDensityPower b Q x * w x) ∂rotationMeasure := by
  have hi := weighted_rotatedDensityPower_integrable_prod hb hw hw0
  calc
    _ ≤ ∫ x, (∫ Q, rotatedDensityPower b Q x * w x ∂rotationMeasure) := by
      apply integral_mono (weighted_fineDensityPower_integrable hb hw hw0) hi.integral_prod_right
      intro x
      change fineDensityPower b (position x) * w x ≤ ∫ Q, rotatedDensityPower b Q x * w x ∂rotationMeasure
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (fineDensityPower_le_angularAverage hb (position x)) (hw0 _)
    _ = _ := (integral_integral_swap hi).symm

theorem fine_density_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : Configuration n, fineDensityPower b (position x) * ‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  let w (s : Spins n) (x : Configuration n) := ‖ψ.value s x‖^2
  have hw (s : Spins n) : Integrable (w s) :=
    (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
  have hw0 (s : Spins n) (x) : 0 ≤ w s x := sq_nonneg _
  let A (Q : Rotation) := ∑ s, ∫ x, rotatedDensityPower b Q x * w s x
  have hAs (s : Spins n) : Integrable (fun Q => ∫ x, rotatedDensityPower b Q x * w s x) rotationMeasure :=
    (weighted_rotatedDensityPower_integrable_prod hb (hw s) (hw0 s)).integral_prod_left
  have hA : Integrable A rotationMeasure := integrable_finsetSum _ (fun s _ => hAs s)
  have hJ : (∑ s, ∫ x, fineDensityPower b (position x) * w s x) ≤ ∫ Q, A Q ∂rotationMeasure := by
    rw [show (∫ Q, A Q ∂rotationMeasure) = ∑ s, ∫ Q, (∫ x, rotatedDensityPower b Q x * w s x) ∂rotationMeasure from
      integral_finsetSum _ (fun s _ => hAs s)]
    exact Finset.sum_le_sum (fun s _ => weighted_fineDensityPower_le_angular hb (hw s) (hw0 s))
  have hpoint (Q : Rotation) : thomasFermiCoefficient * A Q ≤ kinetic ψ +
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ := by
    have H := fixed_rotation_fine_density_kinetic_lower hn ψ hψ hb Q
    exact sub_le_iff_le_add.mp H
  have hI := integral_mono (hA.const_mul thomasFermiCoefficient)
    (integrable_const (kinetic ψ + ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ)) hpoint
  rw [integral_const_mul] at hI
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hI
  have hc : 0 ≤ thomasFermiCoefficient := by
    unfold thomasFermiCoefficient
    positivity
  exact sub_le_iff_le_add.mpr ((mul_le_mul_of_nonneg_left hJ hc).trans hI)

end Coulomb

open MeasureTheory Set
open scoped BigOperators Matrix ENNReal

end

end OAI
