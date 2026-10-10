import OAI.Analysis.CircleDomains.Sobolev.SmoothImageArea
import OAI.Analysis.CircleDomains.Transfer.ExteriorImageCircuit
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! The absolute signed area of a regular Jordan curve is the actual
area of its bounded component. This is a direct specialization of the
remaining signed Green input, with no analytic area theorem assumed. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_signed_area (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    |signedCurveArea γ| = (volume (jordanInterior H)).toReal := by
  obtain ⟨e, he, hg⟩ := hgreen H γ hγ
  have hh := hg 0 Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    univ isOpen_univ (subset_univ _) (fun _ => 0) (fun z => z.re)
    contDiff_const.contDiffOn Complex.reCLM.contDiff.contDiffOn
  have hder (z : ℂ) : fderiv ℝ (fun w : ℂ => w.re) z 1 -
      fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z Complex.I = 1 := by
    change (fderiv ℝ Complex.reCLM z) 1 - _ = 1
    rw [Complex.reCLM.fderiv]
    simp only [fderiv_const_apply, Complex.reCLM_apply, Complex.one_re, zero_apply, sub_zero]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, iUnion_of_empty,
    sdiff_empty, hder, integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one] at hh
  have hform : planarFormIntegral (fun _ => 0) (fun z => z.re) γ = signedCurveArea γ := by
    simp only [planarFormIntegral, signedCurveArea, zero_mul, zero_add]
  rw [hform] at hh
  have habs := congrArg abs hh
  simpa only [abs_mul, he, one_mul, abs_of_nonneg ENNReal.toReal_nonneg] using habs

lemma regular_jordan_signed_area_ne_zero (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    signedCurveArea γ ≠ 0 := by
  have hpos : 0 < volume (jordanInterior H) :=
    (jordanInterior_isOpen H).measure_pos volume (isConnected_jordanInterior H).nonempty
  have hfin : volume (jordanInterior H) ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt
      (isCompact_closure_jordanInterior H).measure_lt_top).ne
  have hr : 0 < (volume (jordanInterior H)).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have he := regular_jordan_signed_area hgreen H γ hγ
  intro hz
  rw [hz, abs_zero] at he
  exact hr.ne' he.symm

end CircleDomainRigidity

end

end OAI
