import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def scalarTube (H : E → ℝ) : Set (E × ℂ) := {p | H p.1 < p.2.im}

def scalarNormalInversion (y : ℝ) (p : E × ℂ) : E × ℂ :=
  (((-I * (y : ℂ)) / p.2) • p.1, -((y : ℂ)^2) / p.2)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma scalarTube_im_pos {H : E → ℝ} (hH : ∀ z, 0 ≤ H z) {p : E × ℂ}
    (hp : p ∈ scalarTube H) : 0 < p.2.im := (hH p.1).trans_lt hp

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma scalarTube_normal_ne_zero {H : E → ℝ} (hH : ∀ z, 0 ≤ H z) {p : E × ℂ}
    (hp : p ∈ scalarTube H) : p.2 ≠ 0 := by
  intro hz
  have h := scalarTube_im_pos hH hp
  simp [hz] at h

lemma scalarNormalInversion_residual (H : E → ℝ)
    (hH : ∀ (c : ℂ) z, H (c • z) = Complex.normSq c * H z)
    (y : ℝ) (p : E × ℂ) :
    (scalarNormalInversion y p).2.im - H (scalarNormalInversion y p).1 =
      (y^2 / Complex.normSq p.2) * (p.2.im - H p.1) := by
  simp only [scalarNormalInversion,hH,Complex.div_im,Complex.normSq_div,
    map_mul,Complex.normSq_neg,Complex.normSq_I,Complex.normSq_ofReal,
    one_mul,Complex.neg_im,Complex.neg_re,pow_two,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma scalarNormalInversion_mem {H : E → ℝ}
    (hH : ∀ (c : ℂ) z, H (c • z) = Complex.normSq c * H z)
    (hnonneg : ∀ z, 0 ≤ H z) {y : ℝ} (hy : y ≠ 0) {p : E × ℂ}
    (hp : p ∈ scalarTube H) : scalarNormalInversion y p ∈ scalarTube H := by
  change H (scalarNormalInversion y p).1 < (scalarNormalInversion y p).2.im
  rw [← sub_pos,scalarNormalInversion_residual H hH]
  exact mul_pos (div_pos (sq_pos_of_ne_zero hy)
    (Complex.normSq_pos.mpr (scalarTube_normal_ne_zero hnonneg hp))) (sub_pos.mpr hp)

lemma scalarNormalInversion_involutive {y : ℝ} (hy : y ≠ 0)
    (p : E × ℂ) (hp : p.2 ≠ 0) :
    scalarNormalInversion y (scalarNormalInversion y p) = p := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  have hI : I * I = -1 := Complex.I_mul_I
  apply Prod.ext
  · change ((-I*(y : ℂ))/(-((y : ℂ)^2)/p.2)) •
      (((-I*(y : ℂ))/p.2) • p.1) = p.1
    rw [smul_smul]
    have hh : ((-I*(y : ℂ))/(-((y : ℂ)^2)/p.2))*((-I*(y : ℂ))/p.2) = 1 := by
      field_simp
      simp [Complex.I_sq]
    rw [hh,one_smul]
  · change -((y : ℂ)^2)/(-((y : ℂ)^2)/p.2) = p.2
    field_simp

lemma scalarNormalInversion_axis {y : ℝ} (hy : y ≠ 0) :
    scalarNormalInversion (E := E) y (0,I*(y : ℂ)) = (0,I*(y : ℂ)) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  apply Prod.ext
  · simp [scalarNormalInversion]
  · change -((y : ℂ)^2)/(I*(y : ℂ)) = I*(y : ℂ)
    field_simp
    simp [Complex.I_sq]

lemma scalarNormalInversion_analytic (y : ℝ) {p : E × ℂ} (hp : p.2 ≠ 0) :
    AnalyticAt ℂ (scalarNormalInversion (E := E) y) p := by
  have hs : AnalyticAt ℂ (fun p : E × ℂ => p.2) p :=
    (ContinuousLinearMap.snd ℂ E ℂ).analyticAt p
  have hf : AnalyticAt ℂ (fun p : E × ℂ => p.1) p :=
    (ContinuousLinearMap.fst ℂ E ℂ).analyticAt p
  exact ((analyticAt_const.div hs hp).smul hf).prod (analyticAt_const.div hs hp)

lemma scalarNormalInversion_fixed_iff {H : E → ℝ}
    (hH : ∀ z, 0 ≤ H z) {y : ℝ} (hy : 0 < y) {p : E × ℂ}
    (hp : p ∈ scalarTube H) :
    scalarNormalInversion y p = p ↔ p = (0,I*(y : ℂ)) := by
  constructor
  · intro he
    have hw : p.2 ≠ 0 := scalarTube_normal_ne_zero hH hp
    have hw' := congrArg Prod.snd he
    change -((y : ℂ)^2)/p.2 = p.2 at hw'
    have hs : p.2^2 = (I*(y : ℂ))^2 := by
      have hsq := (div_eq_iff hw).mp hw'
      rw [mul_pow,Complex.I_sq]
      simpa only [pow_two,neg_one_mul] using hsq.symm
    obtain hwpos | hwneg := sq_eq_sq_iff_eq_or_eq_neg.mp hs
    · have hz := congrArg Prod.fst he
      change ((-I*(y : ℂ))/p.2) • p.1 = p.1 at hz
      have hcoef : (-I*(y : ℂ))/p.2 = -1 := by
        rw [hwpos]
        have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
        field_simp
      rw [hcoef,neg_one_smul] at hz
      have hz0 : p.1 = 0 := by
        have hd : (2 : ℂ) • p.1 = 0 := by
          simpa [two_smul] using (congrArg (fun z : E => p.1+z) hz).symm
        exact (smul_eq_zero.mp hd).resolve_left (by norm_num)
      exact Prod.ext hz0 hwpos
    · have him := scalarTube_im_pos hH hp
      rw [hwneg] at him
      simp only [neg_im,mul_im,I_re,I_im,ofReal_re,ofReal_im,mul_zero,
        zero_add,one_mul] at him
      linarith
  · rintro rfl
    exact scalarNormalInversion_axis hy.ne'

def scalarTubeInvolution (H : E → ℝ)
    (hH : ∀ (c : ℂ) z, H (c • z) = Complex.normSq c * H z)
    (hnonneg : ∀ z, 0 ≤ H z) (y : ℝ) (hy : y ≠ 0) :
    scalarTube H ≃ₜ scalarTube H where
  toFun p := ⟨scalarNormalInversion y p,scalarNormalInversion_mem hH hnonneg hy p.property⟩
  invFun p := ⟨scalarNormalInversion y p,scalarNormalInversion_mem hH hnonneg hy p.property⟩
  left_inv p := Subtype.ext (scalarNormalInversion_involutive hy p.val
    (scalarTube_normal_ne_zero hnonneg p.property))
  right_inv p := Subtype.ext (scalarNormalInversion_involutive hy p.val
    (scalarTube_normal_ne_zero hnonneg p.property))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (scalarNormalInversion_analytic y
      (scalarTube_normal_ne_zero hnonneg p.property)).continuousAt.comp
      continuous_subtype_val.continuousAt
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (scalarNormalInversion_analytic y
      (scalarTube_normal_ne_zero hnonneg p.property)).continuousAt.comp
      continuous_subtype_val.continuousAt

end Release061

end

end OAI
