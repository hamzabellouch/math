import OAI.Analysis.CircleDomains.Sobolev.RegularPieceCoarea
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! Actual scalar coordinate maps with transverse real or imaginary coordinate.
Their Jacobians are the corresponding nonzero scalar partials. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma planar_linear_isInvertible_of_det_ne_zero (A : ℂ →L[ℝ] ℂ) (hA : A.det ≠ 0) :
    A.IsInvertible := by
  have hunit : IsUnit A := ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
    ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA))
  obtain ⟨a, rfl⟩ := hunit
  exact ⟨ContinuousLinearEquiv.ofUnit a, rfl⟩

def scalarLevelCoordinate (f : ℂ → ℝ) (H : ℂ →L[ℝ] ℝ) : ℂ → ℂ :=
  fun z => (f z : ℂ) + H z • Complex.I

def scalarLevelDifferential (L H : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp L + (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).comp H

lemma scalarLevelCoordinate_re (f : ℂ → ℝ) (H : ℂ →L[ℝ] ℝ) (z : ℂ) :
    (scalarLevelCoordinate f H z).re = f z := by
  simp [scalarLevelCoordinate]

lemma hasFDerivAt_scalarLevelCoordinate {f : ℂ → ℝ} {L : ℂ →L[ℝ] ℝ} {z : ℂ}
    (hf : HasFDerivAt f L z) (H : ℂ →L[ℝ] ℝ) :
    HasFDerivAt (scalarLevelCoordinate f H) (scalarLevelDifferential L H) z := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp z hf).add
    ((ContinuousLinearMap.toSpanSingleton ℝ Complex.I).hasFDerivAt.comp z H.hasFDerivAt)

lemma scalarLevelDifferential_det (L H : ℂ →L[ℝ] ℝ) :
    (scalarLevelDifferential L H).det = L 1 * H Complex.I - L Complex.I * H 1 := by
  rw [complex_real_det_columns]
  simp [scalarLevelDifferential, ContinuousLinearMap.toSpanSingleton_apply]

lemma scalarLevelCoordinate_im_isInvertible {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : fderiv ℝ f z 1 ≠ 0) :
    (fderiv ℝ (scalarLevelCoordinate f Complex.imCLM) z).IsInvertible := by
  rw [(hasFDerivAt_scalarLevelCoordinate hf.hasFDerivAt _).fderiv]
  apply planar_linear_isInvertible_of_det_ne_zero
  simpa only [scalarLevelDifferential_det, Complex.imCLM_apply, Complex.I_im,
    Complex.one_im, mul_one, mul_zero, sub_zero] using hz

lemma scalarLevelCoordinate_re_isInvertible {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : fderiv ℝ f z Complex.I ≠ 0) :
    (fderiv ℝ (scalarLevelCoordinate f Complex.reCLM) z).IsInvertible := by
  rw [(hasFDerivAt_scalarLevelCoordinate hf.hasFDerivAt _).fderiv]
  apply planar_linear_isInvertible_of_det_ne_zero
  simpa only [scalarLevelDifferential_det, Complex.reCLM_apply, Complex.I_re,
    Complex.one_re, mul_zero, mul_one, zero_sub, neg_ne_zero] using hz

lemma scalar_regular_im_weighted_coarea {f : ℂ → ℝ} (hf : Continuous f)
    {S : Set ℂ} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    (hd : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hn : ∀ z ∈ S, fderiv ℝ f z 1 ≠ 0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q :=
  regular_map_weighted_coarea hf hS hb (scalarLevelCoordinate_re f Complex.imCLM)
    (fun z hz => (hasFDerivAt_scalarLevelCoordinate (hd z hz).hasFDerivAt _).differentiableAt)
    (fun z hz => scalarLevelCoordinate_im_isInvertible (hd z hz) (hn z hz)) hq

lemma scalar_regular_re_weighted_coarea {f : ℂ → ℝ} (hf : Continuous f)
    {S : Set ℂ} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    (hd : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hn : ∀ z ∈ S, fderiv ℝ f z Complex.I ≠ 0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q :=
  regular_map_weighted_coarea hf hS hb (scalarLevelCoordinate_re f Complex.reCLM)
    (fun z hz => (hasFDerivAt_scalarLevelCoordinate (hd z hz).hasFDerivAt _).differentiableAt)
    (fun z hz => scalarLevelCoordinate_re_isInvertible (hd z hz) (hn z hz)) hq

end CircleDomainRigidity

end

end OAI
