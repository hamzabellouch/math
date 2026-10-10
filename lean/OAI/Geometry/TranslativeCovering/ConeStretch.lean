import OAI.Geometry.TranslativeCovering.LocalizationMeans

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace ConeStretch
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def stretch {n : ℕ} (i : Fin n) (k : ℝ) : Space n →ₗ[ℝ] Space n :=
  Matrix.toEuclideanLin (Matrix.diagonal (fun j => if j = i then k else 1))

lemma stretch_apply {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) (j : Fin n) :
    stretch i k x j = (if j = i then k else 1) * x j := by
  simp [stretch, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

lemma stretch_det {n : ℕ} (i : Fin n) (k : ℝ) :
    LinearMap.det (stretch i k) = k := by
  rw [stretch, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    Matrix.det_diagonal]
  classical
  simp

lemma norm_sq {n : ℕ} (x : Space n) : ‖x‖^2 = ∑ i, (x i)^2 := by
  simpa [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x

lemma stretch_norm_sq {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) :
    ‖stretch i k x‖^2 = ‖x‖^2 + (k^2-1)*(x i)^2 := by
  classical
  rw [norm_sq, norm_sq]
  simp only [stretch_apply]
  calc
    _ = ∑ j : Fin n, ((x j)^2 + if j = i then (k^2-1)*(x i)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j; simp; ring
      · simp [h]
    _ = _ := by simp [Finset.sum_add_distrib]

lemma coordinate_sq_le {n : ℕ} (i : Fin n) (x : Space n) : (x i)^2 ≤ ‖x‖^2 := by
  rw [norm_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

lemma stretch_norm_bounds {n : ℕ} (i : Fin n) {k : ℝ} (hk : 1 ≤ k) (x : Space n) :
    ‖x‖ ≤ ‖stretch i k x‖ ∧ ‖stretch i k x‖ ≤ k*‖x‖ := by
  have hsq := stretch_norm_sq i k x
  have hcoord := coordinate_sq_le i x
  have hk0 : 0 ≤ k := by linarith
  have hk2 : 0 ≤ k^2-1 := by nlinarith
  have hmul := mul_nonneg hk2 (sq_nonneg (x i))
  have hmul2 := mul_nonneg hk2 (sub_nonneg.mpr hcoord)
  constructor
  · nlinarith [norm_nonneg x, norm_nonneg (stretch i k x)]
  · nlinarith [norm_nonneg x, norm_nonneg (stretch i k x), mul_nonneg hk0 (norm_nonneg x)]

lemma stretch_inverse {n : ℕ} (i : Fin n) {k : ℝ} (hk : k ≠ 0) (x : Space n) :
    stretch i k (stretch i k⁻¹ x) = x := by
  ext j
  simp only [stretch_apply]
  split_ifs <;> simp [hk]

def cone {n : ℕ} (i : Fin n) (t R : ℝ) : Set (Space n) :=
  {x | 0 < ‖x‖ ∧ ‖x‖ < R ∧ t*‖x‖ < x i}

lemma threshold_iff {a b x t s k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 0 < k)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hnorm : b^2 = a^2 + (k^2-1)*x^2) :
    s*b < k*x ↔ t*a < x := by
  have hfac : 0 < k^2*(1-s^2)+s^2 := by
    have : 0 < 1-s^2 := by nlinarith
    positivity
  have heq : (k*x)^2-(s*b)^2 = (k^2*(1-s^2)+s^2)*(x^2-(t*a)^2) := by
    calc
      _ = (k^2*(1-s^2)+s^2)*x^2-s^2*a^2 := by rw [mul_pow, mul_pow, hnorm]; ring
      _ = _ := by linear_combination a^2*hrel
  by_cases hx : 0 < x
  · have hkx : 0 ≤ k*x := le_of_lt (mul_pos hk hx)
    rw [← sq_lt_sq₀ (mul_nonneg hs.le hb) hkx,
      ← sq_lt_sq₀ (mul_nonneg ht.le ha) hx.le]
    have hh : 0 < (k^2*(1-s^2)+s^2)*(x^2-(t*a)^2) ↔ 0 < x^2-(t*a)^2 :=
      mul_pos_iff_of_pos_left hfac
    simpa only [← heq, sub_pos] using hh
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    have h1 := mul_nonneg hs.le hb
    have h2 := mul_nonneg ht.le ha
    have h3 := mul_nonpos_of_nonneg_of_nonpos hk.le hx0
    constructor <;> intro h <;> linarith

lemma stretch_threshold {n : ℕ} (i : Fin n) {t s k : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 0 < k)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2) (x : Space n) :
    s*‖stretch i k x‖ < (stretch i k x) i ↔ t*‖x‖ < x i := by
  rw [stretch_apply, ite_eq_left rfl]
  exact threshold_iff (norm_nonneg _) (norm_nonneg _) ht hs hs1 hk hrel
    (stretch_norm_sq i k x)

lemma stretch_cone_lower_norm {n : ℕ} (i : Fin n) {t k r : ℝ}
    (ht : 0 < t) (hk : 1 ≤ k) (hr : 0 ≤ r)
    (hrel : r^2 = 1+(k^2-1)*t^2) {x : Space n} (hx : t*‖x‖ < x i) :
    r*‖x‖ ≤ ‖stretch i k x‖ := by
  have hxi : 0 < x i := lt_of_le_of_lt (mul_nonneg ht.le (norm_nonneg x)) hx
  have hx2 : (t*‖x‖)^2 ≤ (x i)^2 := by
    exact (sq_le_sq₀ (mul_nonneg ht.le (norm_nonneg x)) hxi.le).mpr hx.le
  have hk2 : 0 ≤ k^2-1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hx2 hk2
  have hsq := stretch_norm_sq i k x
  have hrx := mul_nonneg hr (norm_nonneg x)
  have hh : (r*‖x‖)^2 = ‖x‖^2+(k^2-1)*(t*‖x‖)^2 := by
    rw [mul_pow, hrel]; ring
  nlinarith [norm_nonneg (stretch i k x)]

lemma cone_smul {n : ℕ} (i : Fin n) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    cone i t R = R • cone i t 1 := by
  ext y
  constructor
  · intro hy
    refine ⟨R⁻¹ • y, ?_, by simp [hR.ne']⟩
    change 0 < ‖R⁻¹ • y‖ ∧ ‖R⁻¹ • y‖ < 1 ∧ t*‖R⁻¹ • y‖ < (R⁻¹ • y) i
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), PiLp.smul_apply,
      smul_eq_mul]
    change 0 < ‖y‖ ∧ ‖y‖ < R ∧ t*‖y‖ < y i at hy
    refine ⟨mul_pos (inv_pos.mpr hR) hy.1, ?_, ?_⟩
    · nlinarith [mul_lt_mul_of_pos_left hy.2.1 (inv_pos.mpr hR), inv_mul_cancel₀ hR.ne']
    · simpa only [mul_assoc, mul_left_comm t R⁻¹] using
        mul_lt_mul_of_pos_left hy.2.2 (inv_pos.mpr hR)
  · rintro ⟨x, hx, rfl⟩
    change 0 < ‖R • x‖ ∧ ‖R • x‖ < R ∧ t*‖R • x‖ < (R • x) i
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, PiLp.smul_apply, smul_eq_mul]
    change 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t*‖x‖ < x i at hx
    refine ⟨mul_pos hR hx.1, by nlinarith, ?_⟩
    simpa only [mul_assoc, mul_left_comm t R] using mul_lt_mul_of_pos_left hx.2.2 hR

lemma cone_volume_scale {n : ℕ} (i : Fin n) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    volume (cone i t R) = ENNReal.ofReal (R^n) * volume (cone i t 1) := by
  rw [cone_smul i t hR, Measure.addHaar_smul_of_nonneg volume hR.le]
  simp [Space]

lemma stretch_cone_outer {n : ℕ} (i : Fin n) {t s k : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2) :
    stretch i k '' cone i t 1 ⊆ cone i s k := by
  rintro _ ⟨x, hx, rfl⟩
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn := stretch_norm_bounds i hk x
  exact ⟨lt_of_lt_of_le hx.1 hn.1,
    lt_of_le_of_lt hn.2 (by simpa using mul_lt_mul_of_pos_left hx.2.1 hk0),
    (stretch_threshold i ht hs hs1 hk0 hrel x).mpr hx.2.2⟩

lemma stretch_cone_inner {n : ℕ} (i : Fin n) {t s k r : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k) (hr : 0 < r)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hrsq : r^2 = 1+(k^2-1)*t^2) :
    cone i s r ⊆ stretch i k '' cone i t 1 := by
  intro y hy
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  let x := stretch i k⁻¹ y
  have hxy : stretch i k x = y := stretch_inverse i hk0.ne' y
  have ht' : t*‖x‖ < x i := (stretch_threshold i ht hs hs1 hk0 hrel x).mp
    (by simpa only [hxy] using hy.2.2)
  have hlo : r*‖x‖ ≤ ‖y‖ := by
    simpa only [hxy] using stretch_cone_lower_norm i ht hk hr.le hrsq ht'
  refine ⟨x, ⟨?_, ?_, ht'⟩, hxy⟩
  · apply norm_pos_iff.mpr
    intro hx0
    have hy0 : y = 0 := by rw [← hxy, hx0, map_zero]
    have := hy.1
    simp [hy0] at this
  · have := hy.2.1
    nlinarith

lemma cone_volume_comparison {n : ℕ} (i : Fin n) {t s k r : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k) (hr : 0 < r)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hrsq : r^2 = 1+(k^2-1)*t^2) :
    ENNReal.ofReal (r^n)*volume (cone i s 1) ≤
        ENNReal.ofReal k*volume (cone i t 1) ∧
    ENNReal.ofReal k*volume (cone i t 1) ≤
        ENNReal.ofReal (k^n)*volume (cone i s 1) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hm : volume (stretch i k '' cone i t 1) =
      ENNReal.ofReal k*volume (cone i t 1) := by
    rw [Measure.addHaar_image_linearMap, stretch_det, abs_of_pos hk0]
  constructor
  · rw [← cone_volume_scale i s hr, ← hm]
    exact measure_mono (stretch_cone_inner i ht hs hs1 hk hr hrel hrsq)
  · rw [← cone_volume_scale i s hk0, ← hm]
    exact measure_mono (stretch_cone_outer i ht hs hs1 hk hrel)

end ConeStretch

end OAI
