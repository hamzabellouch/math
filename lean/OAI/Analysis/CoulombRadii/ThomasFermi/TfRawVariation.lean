import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfPotential

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
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
noncomputable def tfRawVariation (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f h : TFLp μ) (t : ℝ) : ℝ :=
  c*(∫ x, (f x+t*h x)^(5/3:ℝ) ∂μ) - (L f+t*L h) +
    (B f f+t*(B f h+B h f)+t^2*B h h)/2
omit [IsFiniteMeasure μ] in
lemma tfRawVariation_eq (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f h : TFLp μ}
    (hf : TFNonneg f) (hh : TFNonneg h) {t : ℝ} (ht : 0 ≤ t) :
    tfRawVariation c L B f h t = tfFunctional c L B (f+t • h) := by
  have hK : (∫ x, (f x+t*h x)^(5/3:ℝ) ∂μ) = ‖f+t • h‖^(5/3:ℝ) := by
    rw [← tfLp_nonneg_power (hf.add (hh.smul ht))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • h), Lp.coeFn_smul t h] with x hx hy
    simp only [hx,Pi.add_apply,hy,Pi.smul_apply,smul_eq_mul]
  unfold tfRawVariation tfFunctional
  rw [hK]
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring
lemma tfRawVariation_hasDerivAt (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f h : TFLp μ)
    (hh : ∀ᵐ x ∂μ, |h x| ≤ 1) :
    HasDerivAt (tfRawVariation c L B f h)
      (c*(5/3:ℝ)*(∫ x, (f x)^(2/3:ℝ)*h x ∂μ) - L h + (B f h+B h f)/2) 0 := by
  have hK := tfPower_hasDerivAt (Lp.memLp f) (Lp.memLp h).aestronglyMeasurable hh
  have hid := hasDerivAt_id (0:ℝ)
  have hL := (hasDerivAt_const (0:ℝ) (L f)).add (hid.mul_const (L h))
  have hB := (((hasDerivAt_const (0:ℝ) (B f f)).add
    (hid.mul_const (B f h+B h f))).add ((hid.pow 2).mul_const (B h h))).div_const 2
  convert ((hK.const_mul c).sub hL).add hB using 1 <;>
    first | rfl | (norm_num [tfRawVariation]; ring)
lemma tfFunctional_tangent_nonneg (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f : TFLp μ} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g)
    {h : TFLp μ} (hh : TFNonneg h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) :
    0 ≤ c*(5/3:ℝ)*(∫ x, (f x)^(2/3:ℝ)*h x ∂μ) - L h + (B f h+B h f)/2 := by
  apply nonneg_deriv_of_min_on_right (tfRawVariation_hasDerivAt c L B f h hb)
  intro t ht
  rw [tfRawVariation_eq c L B hf hh (le_refl 0), zero_smul, add_zero,
    tfRawVariation_eq c L B hf hh ht]
  exact hm _ (hf.add (hh.smul ht))
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma tfFunctional_scaling_eq (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f : TFLp μ) {t : ℝ} (ht : 0 ≤ t) :
    tfFunctional c L B (t • f) = c*t^(5/3:ℝ)*‖f‖^(5/3:ℝ) - t*L f + t^2*B f f/2 := by
  unfold tfFunctional
  rw [norm_smul,Real.norm_of_nonneg ht,Real.mul_rpow ht (norm_nonneg _)]
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
lemma tfFunctional_scaling_stationary (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f : TFLp μ} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g) :
    c*(5/3:ℝ)*‖f‖^(5/3:ℝ) - L f+B f f = 0 := by
  let J : ℝ → ℝ := fun t => c*t^(5/3:ℝ)*‖f‖^(5/3:ℝ) - t*L f+t^2*B f f/2
  have hj : IsLocalMin J 1 := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0:ℝ)<1)] with t ht
    have H := hm (t • f) (hf.smul ht.le)
    rw [tfFunctional_scaling_eq c L B f ht.le] at H
    simpa [J,tfFunctional] using H
  have hid := hasDerivAt_id (1:ℝ)
  have hpow := hid.rpow_const (p := (5/3:ℝ)) (Or.inl (by norm_num : (1:ℝ)≠0))
  have hd : HasDerivAt J (c*(5/3:ℝ)*‖f‖^(5/3:ℝ) - L f+B f f) 1 := by
    have H := (((hpow.const_mul c).mul_const (‖f‖^(5/3:ℝ))).sub (hid.mul_const (L f))).add
      (((hid.pow 2).mul_const (B f f)).div_const 2)
    convert H using 1 <;> first | rfl | norm_num [J]
  exact hj.hasDerivAt_eq_zero hd
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
