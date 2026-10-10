import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.PacketStateL2Norm
import OAI.Analysis.CoulombRadii.FormDomain.L2MultiplierDistribution

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
namespace Coulomb
lemma schwartz_fourier_derivative_norm (g : 𝓢(Space,ℂ)) (a ξ : Space) :
    ‖(𝓕 (∂_{a} g) : 𝓢(Space,ℂ)) ξ‖^2 =
      (2*Real.pi*inner ℝ ξ a)^2 * ‖(𝓕 g : 𝓢(Space,ℂ)) ξ‖^2 := by
  have ht : (fun ξ : Space => inner ℝ ξ a).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht]
  change ‖(2 * Real.pi * Complex.I) * ((inner ℝ ξ a : ℂ) * (𝓕 g : 𝓢(Space,ℂ)) ξ)‖^2 = _
  rw [← mul_assoc]
  exact fourierMultiplier_norm_sq _ _

lemma schwartz_fourier_weighted_integrable (g : 𝓢(Space,ℂ)) (a : Space) :
    Integrable (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2 * ‖(𝓕 g : 𝓢(Space,ℂ)) ξ‖^2) := by
  simp_rw [← schwartz_fourier_derivative_norm]
  exact ((𝓕 (∂_{a} g) : 𝓢(Space,ℂ)).memLp 2 volume).integrable_norm_pow (by norm_num)

lemma schwartz_fourier_weighted_integral (g : 𝓢(Space,ℂ)) (a : Space) :
    (∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 * ‖(𝓕 g : 𝓢(Space,ℂ)) ξ‖^2) =
      ∫ x : Space, ‖fderiv ℝ g x a‖^2 := by
  simp_rw [← schwartz_fourier_derivative_norm]
  rw [← schwartz_toL2_norm_sq, SchwartzMap.norm_fourier_toL2_eq, schwartz_toL2_norm_sq]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]

lemma packetState_fourier_apply (g : 𝓢(Space,ℂ)) (y p ξ : Space) :
    (𝓕 (packetState g y p) : 𝓢(Space,ℂ)) ξ =
      Complex.exp ((-2*Real.pi*inner ℝ y (ξ-p) : ℝ)*Complex.I) * (𝓕 g : 𝓢(Space,ℂ)) (ξ-p) := by
  rw [packetState, FourierTransform.fourier_fourierInv_eq]
  change (𝓕 (SchwartzMap.compSubConstCLM ℂ y g) : 𝓢(Space,ℂ)) (ξ-p) = _
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ Space) (⇑g) (-y)) (ξ-p)
  have hh : (⇑g ∘ fun v => v + -y) = (SchwartzMap.compSubConstCLM ℂ y g : Space → ℂ) := by
    ext v; simp [sub_eq_add_neg]
  rw [hh] at ht
  change 𝓕 (⇑(SchwartzMap.compSubConstCLM ℂ y g)) (ξ-p) =
    Real.fourierChar (inner ℝ (-y) (ξ-p)) • 𝓕 (⇑g) (ξ-p) at ht
  simpa [SchwartzMap.fourier_coe, Circle.smul_def, Real.fourierChar_apply, inner_neg_left,
    neg_mul, mul_neg] using ht

lemma packetState_fourier_joint_continuous (g : 𝓢(Space,ℂ)) :
    Continuous (fun z : (Space × Space) × Space =>
      (𝓕 (packetState g z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2) := by
  simp only [packetState_fourier_apply]
  fun_prop
end Coulomb

end

end OAI
