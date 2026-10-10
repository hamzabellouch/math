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
namespace Coulomb
lemma modulated_real_derivative_norm (G : Space → ℝ) (hG : Differentiable ℝ G)
    (y p x a : Space) :
    ‖fderiv ℝ (fun z : Space => Complex.exp ((2*Real.pi*inner ℝ z p : ℝ)*Complex.I) *
      (G (z-y) : ℂ)) x a‖^2 =
      (2*Real.pi*inner ℝ a p)^2 * G (x-y)^2 + (fderiv ℝ G (x-y) a)^2 := by
  have hθ := ((Complex.ofRealCLM.hasFDerivAt.comp x
    (((innerSL ℝ).flip p).hasFDerivAt.const_mul (2*Real.pi)))).mul_const Complex.I
  have hq := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hG (x-y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))
  have H := congrArg (fun L : Space →L[ℝ] ℂ => L a) (hθ.cexp.mul hq).fderiv
  have hd : fderiv ℝ (fun z : Space => Complex.exp ((2*Real.pi*inner ℝ z p : ℝ)*Complex.I) *
      (G (z-y) : ℂ)) x a =
      Complex.exp ((2*Real.pi*inner ℝ x p : ℝ)*Complex.I) *
        ((fderiv ℝ G (x-y) a : ℂ) + (2*Real.pi*inner ℝ a p*G (x-y) : ℝ)*Complex.I) := by
    calc
      _ = _ := H
      _ = _ := by
        simp only [add_apply, smul_apply,
          ContinuousLinearMap.comp_apply, Function.comp_apply, id_eq,
          ContinuousLinearMap.id_apply,
          Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply,
          smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
  rw [hd, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero, Real.exp_zero, one_mul]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring
end Coulomb

end

end OAI
