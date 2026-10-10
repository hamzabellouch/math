import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.ModulatedRealDerivativeNorm
import OAI.Analysis.CoulombRadii.FormDomain.SchwartzFourierDerivativeNorm

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
noncomputable def complexWindow (g : 𝓢(Space,ℝ)) : 𝓢(Space,ℂ) :=
  g.postcompCLM Complex.ofRealCLM
@[simp] lemma complexWindow_apply (g : 𝓢(Space,ℝ)) (x : Space) :
    complexWindow g x = (g x : ℂ) := rfl

lemma packetState_real_derivative_norm (g : 𝓢(Space,ℝ)) (y p x a : Space) :
    ‖fderiv ℝ (packetState (complexWindow g) y p) x a‖^2 =
      (2*Real.pi*inner ℝ a p)^2 * g (x-y)^2 + (fderiv ℝ g (x-y) a)^2 := by
  have he : (packetState (complexWindow g) y p : Space → ℂ) =
      fun z => Complex.exp ((2*Real.pi*inner ℝ z p : ℝ)*Complex.I) * (g (z-y) : ℂ) := by
    ext z; rw [packetState_apply, complexWindow_apply]
  rw [he]
  exact modulated_real_derivative_norm g g.differentiable y p x a

lemma real_schwartz_derivative_square_integrable (g : 𝓢(Space,ℝ)) (a : Space) :
    Integrable (fun x : Space => (fderiv ℝ g x a)^2) := by
  have h := ((∂_{a} g : 𝓢(Space,ℝ)).memLp 2 volume).integrable_norm_pow (by norm_num)
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, Real.norm_eq_abs, sq_abs] using h

lemma packetState_real_kinetic_integral (g : 𝓢(Space,ℝ)) (y p a : Space) :
    (∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
      ‖(𝓕 (packetState (complexWindow g) y p) : 𝓢(Space,ℂ)) ξ‖^2) =
      (2*Real.pi*inner ℝ a p)^2 * (∫ x : Space, g x^2) +
        ∫ x : Space, (fderiv ℝ g x a)^2 := by
  rw [schwartz_fourier_weighted_integral]
  simp only [packetState_real_derivative_norm]
  have hG : Integrable (fun x : Space => g x^2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (g.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hD := real_schwartz_derivative_square_integrable g a
  rw [integral_add ((hG.comp_sub_right y).const_mul _) (hD.comp_sub_right y),
    integral_const_mul, integral_sub_right_eq_self (fun x : Space => g x^2) y,
    integral_sub_right_eq_self (fun x : Space => (fderiv ℝ g x a)^2) y]

lemma packetState_fourier_joint_square_integrable (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Integrable (fun z : (Space × Space) × Space =>
      ‖(𝓕 (packetState g z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2‖^2) (μ.prod volume) := by
  have hm := (packetState_fourier_joint_continuous g).norm.pow 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun yp =>
    ((𝓕 (packetState g yp.1 yp.2) : 𝓢(Space,ℂ)).memLp 2 volume).integrable_norm_pow (by norm_num)), ?_⟩
  have he (yp : Space × Space) :
      (∫ ξ : Space, ‖(𝓕 (packetState g yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2) =
        ∫ x : Space, ‖g x‖^2 := by
    rw [← schwartz_toL2_norm_sq, SchwartzMap.norm_fourier_toL2_eq, schwartz_toL2_norm_sq,
      packetState_integral_norm_sq]
  change Integrable (fun yp : Space × Space =>
    ∫ ξ : Space, ‖‖(𝓕 (packetState g yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2‖) μ
  simpa only [Real.norm_of_nonneg (sq_nonneg (_ : ℝ)), he] using
    (integrable_const (∫ x : Space, ‖g x‖^2) : Integrable (fun _ : Space × Space => ∫ x : Space, ‖g x‖^2) μ)

lemma packetState_real_weighted_joint_integrable (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space) :
    Integrable (fun z : (Space × Space) × Space => (2*Real.pi*inner ℝ z.2 a)^2 *
      ‖(𝓕 (packetState (complexWindow g) z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2‖^2) (μ.prod volume) := by
  have hm : Continuous (fun z : (Space × Space) × Space => (2*Real.pi*inner ℝ z.2 a)^2 *
      ‖(𝓕 (packetState (complexWindow g) z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2‖^2) := by
    have hc : Continuous (fun z : (Space × Space) × Space => (2*Real.pi*inner ℝ z.2 a)^2) := by fun_prop
    exact hc.mul ((packetState_fourier_joint_continuous _).norm.pow 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  have hi (yp : Space × Space) : Integrable (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2 *
      ‖(𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2) :=
    schwartz_fourier_weighted_integrable (packetState (complexWindow g) yp.1 yp.2) a
  refine ⟨Filter.Eventually.of_forall hi, ?_⟩
  change Integrable (fun yp : Space × Space => ∫ ξ : Space, ‖(2*Real.pi*inner ℝ ξ a)^2 *
    ‖(𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2‖) μ
  simp only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg (_ : ℝ)) (sq_nonneg (_ : ℝ))),
    packetState_real_kinetic_integral]
  have hpa := hp.continuousLinearMap_comp ((2*Real.pi) • (innerSL ℝ a))
  have hi : Integrable (fun yp : Space × Space => (2*Real.pi*inner ℝ a yp.2)^2) μ := by
    simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      Function.comp_apply, Real.norm_eq_abs, sq_abs] using hpa.integrable_norm_pow (by norm_num)
  exact (hi.mul_const _).add (integrable_const _)
end Coulomb

end

end OAI
