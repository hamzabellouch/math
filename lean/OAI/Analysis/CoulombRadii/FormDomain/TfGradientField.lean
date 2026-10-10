import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfRawVariation

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
noncomputable def tfGradientField (c : ℝ) (W : TFLq (volume.restrict Ω))
    (f : TFLp (volume.restrict Ω)) : TFLq (volume.restrict Ω) :=
  (c*(5/3:ℝ)) • tfKineticField f-W+tfPotentialField hΩ f
lemma tfGradientField_coe (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfGradientField hΩ c W f =ᵐ[volume.restrict Ω]
      (fun x => c*(5/3:ℝ)*(f x)^(2/3:ℝ)-W x+tfPotential f x) := by
  filter_upwards [Lp.coeFn_add ((c*(5/3:ℝ)) • tfKineticField f-W) (tfPotentialField hΩ f),
    Lp.coeFn_sub ((c*(5/3:ℝ)) • tfKineticField f) W,
    Lp.coeFn_smul (c*(5/3:ℝ)) (tfKineticField f),tfKineticField_coe f,
    tfPotentialField_coe hΩ f,hf] with x ha hs hm hk hp hx
  simp only [tfGradientField,ha,Pi.add_apply,hs,Pi.sub_apply,hm,Pi.smul_apply,
    smul_eq_mul,hk,Real.norm_of_nonneg hx,hp]
lemma tfGradientField_pair (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (h : TFLp (volume.restrict Ω)) :
    tfFieldContinuous (tfGradientField hΩ c W f) h =
      c*(5/3:ℝ)*(∫ x in Ω, (f x)^(2/3:ℝ)*h x) - tfFieldContinuous W h+tfCoulomb Ω h f := by
  unfold tfGradientField
  simp only [map_add,map_sub,map_smul,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,smul_eq_mul]
  rw [tfKineticField_pair hf,tfCoulomb_eq_field hΩ h f]
lemma tfGradientField_nonneg (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω, 0 ≤ tfGradientField hΩ c W f x := by
  apply tfDual_nonneg
  intro h hh hb
  rw [tfGradientField_pair hΩ c W hf]
  have H := tfFunctional_tangent_nonneg c (tfFieldContinuous W) (tfCoulombContinuous hΩ) hf hm hh hb
  change 0 ≤ c*(5/3:ℝ)*(∫ x in Ω, (f x)^(2/3:ℝ)*h x) - tfFieldContinuous W h +
    (tfCoulomb Ω f h+tfCoulomb Ω h f)/2 at H
  rw [tfCoulomb_symm f h] at H
  linarith
lemma tfGradientField_self (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    tfFieldContinuous (tfGradientField hΩ c W f) f = 0 := by
  rw [tfGradientField_pair hΩ c W hf,←tfKineticField_pair hf f,tfKineticField_self hf]
  exact tfFunctional_scaling_stationary c (tfFieldContinuous W) (tfCoulombContinuous hΩ) hf hm
lemma tfGradientField_complementarity (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω, tfGradientField hΩ c W f x*f x = 0 := by
  have hn : 0 ≤ᵐ[volume.restrict Ω] (fun x => tfGradientField hΩ c W f x*f x) := by
    filter_upwards [tfGradientField_nonneg hΩ c W hf hm,hf] with x hx hy
    exact mul_nonneg hx hy
  apply (integral_eq_zero_iff_of_nonneg_ae hn (tfFieldPairing_integrable _ _)).mp
  exact tfGradientField_self hΩ c W hf hm
lemma tfEuler_complementarity (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω,
      0 ≤ c*(5/3:ℝ)*(f x)^(2/3:ℝ)-W x+tfPotential f x ∧
      (c*(5/3:ℝ)*(f x)^(2/3:ℝ)-W x+tfPotential f x)*f x = 0 := by
  filter_upwards [tfGradientField_coe hΩ c W hf,tfGradientField_nonneg hΩ c W hf hm,
    tfGradientField_complementarity hΩ c W hf hm] with x he hn hz
  simpa only [he] using And.intro hn hz
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
