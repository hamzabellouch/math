import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryCompactCauchy

lemma norm_cauchy {f g : ℝ → ℂ} {l r : ℝ}
    (hf : ContinuousOn f (Icc l r)) (hg : ContinuousOn g (Icc l r)) :
    (∫ t in Icc l r, ‖f t‖*‖g t‖) ≤
      Real.sqrt (∫ t in Icc l r, ‖f t‖^2)*
        Real.sqrt (∫ t in Icc l r, ‖g t‖^2) := by
  have hfp : MemLp f 2 (volume.restrict (Icc l r)) :=
    (memLp_two_iff_integrable_sq_norm hf.integrableOn_Icc.aestronglyMeasurable).mpr
      (hf.norm.pow 2).integrableOn_Icc
  have hgp : MemLp g 2 (volume.restrict (Icc l r)) :=
    (memLp_two_iff_integrable_sq_norm hg.integrableOn_Icc.aestronglyMeasurable).mpr
      (hg.norm.pow 2).integrableOn_Icc
  have hh : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  simpa only [ENNReal.ofReal_ofNat,Real.rpow_two,Real.sqrt_eq_rpow]
    using integral_mul_norm_le_Lp_mul_Lq hh (by simpa using hfp) (by simpa using hgp)

lemma rectangle_integrable {f : ℝ × ℝ → ℝ} {a b l r : ℝ}
    (hf : ContinuousOn f (Icc a b ×ˢ Icc l r)) :
    Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc l r))) := by
  rw [Measure.prod_restrict]
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf

lemma rectangle_swap {f : ℝ → ℝ → ℝ} {a b l r : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc l r)) :
    (∫ x in Icc a b, ∫ t in Icc l r, f x t) =
      ∫ t in Icc l r, ∫ x in Icc a b, f x t :=
  integral_integral_swap (rectangle_integrable hf)

lemma norm_integral_bound {g : ℝ → ℂ} {l r E : ℝ} (hlr : l≤r)
    (hg : ContinuousOn g (Icc l r)) (hE : (∫t in Icc l r, ‖g t‖^2)≤E) :
    (∫ t in Icc l r, ‖g t‖) ≤ Real.sqrt (r-l)*Real.sqrt E := by
  have hh := norm_cauchy (f:=fun _ => (1:ℂ)) continuousOn_const hg
  simp only [norm_one,one_mul,one_pow,MeasureTheory.integral_const,smul_eq_mul,mul_one] at hh
  have hm : (volume.restrict (Icc l r)) Set.univ = ENNReal.ofReal (r-l) := by simp
  rw [Measure.real,hm,ENNReal.toReal_ofReal (sub_nonneg.mpr hlr)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _))

end OrdinaryCompactCauchy

end

end OAI
