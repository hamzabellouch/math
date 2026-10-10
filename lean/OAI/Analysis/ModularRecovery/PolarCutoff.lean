import OAI.Analysis.ModularRecovery.TomitaResolvent

namespace OAI

/-! Continuous functional calculus and bounded polar truncation in C*-algebras. -/

universe uA

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace BoundedRecovery

def cutoffFunction (K r : ℝ) : ℝ := K / max K (Real.sqrt r)

lemma cutoffFunction_continuous {K : ℝ} (hK : 0 < K) :
    Continuous (cutoffFunction K) := by
  unfold cutoffFunction
  exact continuous_const.div (continuous_const.max Real.continuous_sqrt)
    (fun r => ne_of_gt (lt_of_lt_of_le hK (le_max_left _ _)))

lemma cutoffFunction_nonneg {K r : ℝ} (hK : 0 < K) :
    0 ≤ cutoffFunction K r := by
  exact div_nonneg hK.le (le_trans hK.le (le_max_left _ _))

lemma cutoffFunction_le_one {K r : ℝ} (hK : 0 < K) :
    cutoffFunction K r ≤ 1 := by
  exact (div_le_one (lt_of_lt_of_le hK (le_max_left _ _))).mpr (le_max_left _ _)

lemma cutoffFunction_eq_one {K r : ℝ} (hK : 0 < K) (hr : Real.sqrt r ≤ K) :
    cutoffFunction K r = 1 := by
  simp [cutoffFunction, max_eq_left hr, ne_of_gt hK]

lemma cutoffFunction_norm_bound {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) :
    cutoffFunction K r * r * cutoffFunction K r ≤ K ^ 2 := by
  have hs := Real.sq_sqrt hr
  by_cases h : Real.sqrt r ≤ K
  · rw [cutoffFunction_eq_one hK h]
    simp only [one_mul, mul_one]
    nlinarith [Real.sqrt_nonneg r]
  · have ht : 0 < Real.sqrt r := lt_trans hK (lt_of_not_ge h)
    rw [cutoffFunction, max_eq_right (le_of_not_ge h)]
    have heq : K / Real.sqrt r * r * (K / Real.sqrt r) = K ^ 2 := by
      field_simp
      nlinarith [hs]
    exact heq.le

lemma cutoffFunction_error_bound {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) :
    (1 - cutoffFunction K r) * r * (1 - cutoffFunction K r) ≤ r ^ 2 / K ^ 2 := by
  have hq0 := cutoffFunction_nonneg (r := r) hK
  have hq1 := cutoffFunction_le_one (r := r) hK
  by_cases h : Real.sqrt r ≤ K
  · rw [cutoffFunction_eq_one hK h]
    simp only [sub_self, zero_mul, mul_zero]
    positivity
  · have hKr : K ^ 2 ≤ r := by
      have hs := Real.sq_sqrt hr
      nlinarith [Real.sqrt_nonneg r]
    have hsq : (1 - cutoffFunction K r) ^ 2 ≤ 1 := by nlinarith
    calc
      (1 - cutoffFunction K r) * r * (1 - cutoffFunction K r) =
          r * (1 - cutoffFunction K r) ^ 2 := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hsq hr
      _ ≤ r ^ 2 / K ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hKr hr]

section CStarCutoff

variable {A : Type uA} [CStarAlgebra A]

def polarCutoff (z : A) (K : ℝ) : A := z * cfc (cutoffFunction K) (star z * z)

lemma polarCutoff_square (z : A) {K : ℝ} (hK : 0 < K) :
    star (polarCutoff z K) * polarCutoff z K =
      cfc (fun r => cutoffFunction K r * r * cutoffFunction K r) (star z * z) := by
  have hc := cutoffFunction_continuous hK
  have ha : IsSelfAdjoint (star z * z) := by
    simp [IsSelfAdjoint]
  have hq : IsSelfAdjoint (cfc (cutoffFunction K) (star z * z)) := IsSelfAdjoint.cfc
  rw [cfc_mul (fun r => cutoffFunction K r * r) (cutoffFunction K) (star z * z)
      (hc.mul continuous_id).continuousOn hc.continuousOn,
    cfc_mul (cutoffFunction K) (fun r => r) (star z * z)
      hc.continuousOn continuous_id.continuousOn, cfc_id' ℝ _ ha]
  simp only [polarCutoff, star_mul, hq.star_eq]
  noncomm_ring

lemma polarCutoff_error_square (z : A) {K : ℝ} (hK : 0 < K) :
    star (z - polarCutoff z K) * (z - polarCutoff z K) =
      cfc (fun r => (1 - cutoffFunction K r) * r * (1 - cutoffFunction K r))
        (star z * z) := by
  have hc : Continuous (fun r => 1 - cutoffFunction K r) :=
    continuous_const.sub (cutoffFunction_continuous hK)
  have ha : IsSelfAdjoint (star z * z) := by
    simp [IsSelfAdjoint]
  have hq : IsSelfAdjoint (cfc (cutoffFunction K) (star z * z)) := IsSelfAdjoint.cfc
  rw [cfc_mul (fun r => (1 - cutoffFunction K r) * r) (fun r => 1 - cutoffFunction K r)
      (star z * z) (hc.mul continuous_id).continuousOn hc.continuousOn,
    cfc_mul (fun r => 1 - cutoffFunction K r) (fun r => r) (star z * z)
      hc.continuousOn continuous_id.continuousOn, cfc_id' ℝ _ ha,
    cfc_sub _ _ _ continuous_const.continuousOn (cutoffFunction_continuous hK).continuousOn,
    cfc_const _ _ ha]
  simp only [map_one, polarCutoff, star_sub, star_mul, hq.star_eq]
  noncomm_ring

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_polarCutoff_le (z : A) {K : ℝ} (hK : 0 < K) :
    ‖polarCutoff z K‖ ≤ K := by
  have hh : ‖star (polarCutoff z K) * polarCutoff z K‖ ≤ K ^ 2 := by
    rw [polarCutoff_square z hK]
    apply norm_cfc_le (sq_nonneg K)
    intro r hr
    have hpos : 0 ≤ r := spectrum_nonneg_of_nonneg (star_mul_self_nonneg z) hr
    have hq := cutoffFunction_nonneg (r := r) hK
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cutoffFunction_norm_bound hK hpos
  rw [CStarRing.norm_star_mul_self] at hh
  nlinarith [norm_nonneg (polarCutoff z K)]

lemma polarCutoff_error_le (z : A) {K : ℝ} (hK : 0 < K) :
    star (z - polarCutoff z K) * (z - polarCutoff z K) ≤
      (K ^ 2)⁻¹ • (star z * z) ^ 2 := by
  have ha : IsSelfAdjoint (star z * z) := by
    simp [IsSelfAdjoint]
  rw [polarCutoff_error_square z hK, ← cfc_pow_id (R := ℝ) _ 2 ha,
    ← cfc_const_mul (K ^ 2)⁻¹ (fun r : ℝ => r ^ 2) (star z * z)]
  have hc : Continuous (fun r => 1 - cutoffFunction K r) :=
    continuous_const.sub (cutoffFunction_continuous hK)
  apply cfc_mono (hf := ((hc.mul continuous_id).mul hc).continuousOn)
    (hg := (continuous_const.mul (continuous_id.pow 2)).continuousOn)
  intro r hr
  have hpos : 0 ≤ r := spectrum_nonneg_of_nonneg (star_mul_self_nonneg z) hr
  simpa [div_eq_mul_inv, mul_comm] using cutoffFunction_error_bound hK hpos

end CStarCutoff

end BoundedRecovery

namespace BoundedRecovery

def cutoffLeftFunction (K r : ℝ) : ℝ :=
  Real.sqrt ((1 - cutoffFunction K r) / max K (Real.sqrt r))

def cutoffRightFunction (K r : ℝ) : ℝ :=
  Real.sqrt ((1 - cutoffFunction K r) * max K (Real.sqrt r))

lemma cutoffLeftFunction_continuous {K : ℝ} (hK : 0 < K) :
    Continuous (cutoffLeftFunction K) := by
  unfold cutoffLeftFunction
  exact Real.continuous_sqrt.comp ((continuous_const.sub (cutoffFunction_continuous hK)).div
    (continuous_const.max Real.continuous_sqrt)
    (fun r => ne_of_gt (lt_of_lt_of_le hK (le_max_left _ _))))

lemma cutoffRightFunction_continuous {K : ℝ} (hK : 0 < K) :
    Continuous (cutoffRightFunction K) := by
  unfold cutoffRightFunction
  exact Real.continuous_sqrt.comp ((continuous_const.sub (cutoffFunction_continuous hK)).mul
    (continuous_const.max Real.continuous_sqrt))

lemma cutoffLeftFunction_sq {K r : ℝ} (hK : 0 < K) :
    cutoffLeftFunction K r ^ 2 = (1 - cutoffFunction K r) / max K (Real.sqrt r) := by
  apply Real.sq_sqrt
  exact div_nonneg (sub_nonneg.mpr (cutoffFunction_le_one hK))
    (le_trans hK.le (le_max_left _ _))

lemma cutoffRightFunction_sq {K r : ℝ} (hK : 0 < K) :
    cutoffRightFunction K r ^ 2 = (1 - cutoffFunction K r) * max K (Real.sqrt r) := by
  apply Real.sq_sqrt
  exact mul_nonneg (sub_nonneg.mpr (cutoffFunction_le_one hK))
    (le_trans hK.le (le_max_left _ _))

lemma cutoffLeftFunction_mul_right {K r : ℝ} (hK : 0 < K) :
    cutoffLeftFunction K r * cutoffRightFunction K r = 1 - cutoffFunction K r := by
  have hm : max K (Real.sqrt r) ≠ 0 := ne_of_gt (lt_of_lt_of_le hK (le_max_left _ _))
  have hs : (cutoffLeftFunction K r * cutoffRightFunction K r) ^ 2 =
      (1 - cutoffFunction K r) ^ 2 := by
    rw [mul_pow, cutoffLeftFunction_sq hK, cutoffRightFunction_sq hK]
    field_simp
  have h1 : 0 ≤ cutoffLeftFunction K r * cutoffRightFunction K r :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 := cutoffFunction_le_one (r := r) hK
  nlinarith

lemma cutoff_right_loss {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) :
    (2*K) * cutoffRightFunction K r ^ 2 ≤ r - cutoffFunction K r * r * cutoffFunction K r := by
  rw [cutoffRightFunction_sq hK]
  by_cases h : Real.sqrt r ≤ K
  · simp [cutoffFunction_eq_one hK h]
  · have ht : 0 < Real.sqrt r := hK.trans (lt_of_not_ge h)
    rw [cutoffFunction, max_eq_right (le_of_not_ge h)]
    have hs := Real.sq_sqrt hr
    apply (le_of_sub_nonneg ?_)
    have he : r - K / Real.sqrt r * r * (K / Real.sqrt r) -
        (2*K) * ((1-K / Real.sqrt r) * Real.sqrt r) = (Real.sqrt r - K)^2 := by
      field_simp
      nlinarith [hs]
    rw [he]
    positivity

lemma cutoff_left_loss {K r : ℝ} (hK : 0 < K) :
    (2*K) * cutoffLeftFunction K r ^ 2 ≤ 1 - cutoffFunction K r ^ 2 := by
  rw [cutoffLeftFunction_sq hK]
  have hm : 0 < max K (Real.sqrt r) := lt_of_lt_of_le hK (le_max_left _ _)
  rw [cutoffFunction]
  have he : 1 - (K / max K (Real.sqrt r)) ^ 2 -
      (2*K) * ((1-K / max K (Real.sqrt r)) / max K (Real.sqrt r)) =
      (1 - K / max K (Real.sqrt r)) ^ 2 := by ring
  exact le_of_sub_nonneg (he.symm ▸ sq_nonneg _)

section CStar
variable {A : Type uA} [CStarAlgebra A]

def cutoffLeft (a : A) (K : ℝ) : A :=
  a * cfc (cutoffLeftFunction K) (star a * a)

def cutoffRight (a : A) (K : ℝ) : A :=
  cfc (cutoffRightFunction K) (star a * a)

lemma cutoffLeft_mul_right (a : A) {K : ℝ} (hK : 0 < K) :
    cutoffLeft a K * cutoffRight a K = a - polarCutoff a K := by
  have ha : IsSelfAdjoint (star a * a) := by simp [IsSelfAdjoint]
  rw [cutoffLeft, cutoffRight, mul_assoc, ← cfc_mul _ _ _
    (cutoffLeftFunction_continuous hK).continuousOn (cutoffRightFunction_continuous hK).continuousOn]
  have hf : (fun r => cutoffLeftFunction K r * cutoffRightFunction K r) =
      (fun r => 1 - cutoffFunction K r) := funext (fun _ => cutoffLeftFunction_mul_right hK)
  rw [hf, cfc_sub _ _ _ continuous_const.continuousOn (cutoffFunction_continuous hK).continuousOn,
    cfc_const _ _ ha]
  simp [polarCutoff, mul_sub]

variable [PartialOrder A] [StarOrderedRing A]

lemma cutoffRight_loss (a : A) {K : ℝ} (hK : 0 < K) :
    (2*K) • (star (cutoffRight a K) * cutoffRight a K) ≤
      star a * a - star (polarCutoff a K) * polarCutoff a K := by
  have ha : IsSelfAdjoint (star a * a) := by simp [IsSelfAdjoint]
  have hr : IsSelfAdjoint (cutoffRight a K) := IsSelfAdjoint.cfc
  have heL : (2*K) • (star (cutoffRight a K) * cutoffRight a K) =
      cfc (fun r => (2*K) * cutoffRightFunction K r ^ 2) (star a * a) := by
    rw [cfc_const_mul (2*K) (fun r => cutoffRightFunction K r ^ 2) (star a * a)
      ((cutoffRightFunction_continuous hK).pow 2).continuousOn,
      cfc_pow (cutoffRightFunction K) 2 (star a * a)
        (cutoffRightFunction_continuous hK).continuousOn, hr.star_eq]
    simp only [cutoffRight, pow_two]
  have heR : star a * a - star (polarCutoff a K) * polarCutoff a K =
      cfc (fun r => r - cutoffFunction K r * r * cutoffFunction K r) (star a * a) := by
    rw [cfc_sub (fun r : ℝ => r) (fun r => cutoffFunction K r * r * cutoffFunction K r)
      (star a * a) continuous_id.continuousOn
      (((cutoffFunction_continuous hK).mul continuous_id).mul (cutoffFunction_continuous hK)).continuousOn,
      cfc_id' ℝ _ ha, polarCutoff_square a hK]
  rw [heL, heR]
  apply cfc_mono
    (hf := (continuous_const.mul ((cutoffRightFunction_continuous hK).pow 2)).continuousOn)
    (hg := (continuous_id.sub (((cutoffFunction_continuous hK).mul continuous_id).mul
      (cutoffFunction_continuous hK))).continuousOn)
  intro r hr
  exact cutoff_right_loss hK (spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) hr)

lemma cutoffLeft_loss (a : A) {K : ℝ} (hK : 0 < K) :
    (2*K) • (cutoffLeft a K * star (cutoffLeft a K)) ≤
      a * star a - polarCutoff a K * star (polarCutoff a K) := by
  have ha : IsSelfAdjoint (star a * a) := by simp [IsSelfAdjoint]
  have hl : IsSelfAdjoint (cfc (cutoffLeftFunction K) (star a * a)) := IsSelfAdjoint.cfc
  have hq : IsSelfAdjoint (cfc (cutoffFunction K) (star a * a)) := IsSelfAdjoint.cfc
  have hi : (2*K) • (cfc (cutoffLeftFunction K) (star a * a)) ^ 2 ≤
      1 - (cfc (cutoffFunction K) (star a * a)) ^ 2 := by
    have heL : (2*K) • (cfc (cutoffLeftFunction K) (star a * a)) ^ 2 =
        cfc (fun r => (2*K) * cutoffLeftFunction K r ^ 2) (star a * a) := by
      rw [cfc_const_mul (2*K) (fun r => cutoffLeftFunction K r ^ 2) (star a * a)
        ((cutoffLeftFunction_continuous hK).pow 2).continuousOn,
        cfc_pow (cutoffLeftFunction K) 2 (star a * a)
          (cutoffLeftFunction_continuous hK).continuousOn]
    have heR : 1 - (cfc (cutoffFunction K) (star a * a)) ^ 2 =
        cfc (fun r => 1 - cutoffFunction K r ^ 2) (star a * a) := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun r => cutoffFunction K r ^ 2) (star a * a)
        continuous_const.continuousOn ((cutoffFunction_continuous hK).pow 2).continuousOn,
        cfc_const _ _ ha, map_one, cfc_pow (cutoffFunction K) 2 (star a * a)
          (cutoffFunction_continuous hK).continuousOn]
    rw [heL, heR]
    apply cfc_mono
      (hf := (continuous_const.mul ((cutoffLeftFunction_continuous hK).pow 2)).continuousOn)
      (hg := (continuous_const.sub ((cutoffFunction_continuous hK).pow 2)).continuousOn)
    intro r _hr
    exact cutoff_left_loss hK
  have hh := star_right_conjugate_le_conjugate hi a
  simpa only [cutoffLeft, polarCutoff, star_mul, hl.star_eq, hq.star_eq, pow_two,
    mul_smul_comm, smul_mul_assoc, mul_sub, mul_one, sub_mul, mul_assoc] using hh

end CStar
end BoundedRecovery

end

end OAI
