import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

noncomputable def divergence (P R : X → ℝ) : ℝ :=
  ∑ x, P x * Real.log (P x / R x)

lemma mul_log_div_ge_sub {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hs : 0 < p → 0 < r) : p - r ≤ p * Real.log (p / r) := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · simp only [zero_sub, zero_mul]
    exact neg_nonpos.mpr hr
  · have hr := hs hp
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hr hp)) hp.le
    rw [Real.log_div hr.ne' hp.ne'] at h
    rw [Real.log_div hp.ne' hr.ne']
    have he : p * (r / p - 1) = r - p := by field_simp
    rw [he] at h
    nlinarith

lemma mass_sub_le_divergence (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x) - (∑ x, R x) ≤ divergence P R := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => mul_log_div_ge_sub (hP x) (hR x) (hs x)

lemma divergence_nonneg (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1) (hRsum : ∑ x, R x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) : 0 ≤ divergence P R := by
  simpa only [hPsum, hRsum, sub_self] using mass_sub_le_divergence P R hP hR hs

lemma normalizer_pos (P R : X → ℝ) (_hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    0 < ∑ x, R x * Real.exp (g x) := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun x _ => h x)
    linarith
  exact (mul_pos (hs x hx) (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun y _ => mul_nonneg (hR y) (Real.exp_nonneg _)) (Finset.mem_univ x))

theorem entropy_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    ∑ x, P x * g x ≤ divergence P R + Real.log (∑ x, R x * Real.exp (g x)) := by
  let Z := ∑ x, R x * Real.exp (g x)
  have hZ : 0 < Z := normalizer_pos P R hP hR hPsum hs g
  let R' := fun x => R x * Real.exp (g x) / Z
  have hR' : ∀ x, 0 ≤ R' x := fun x => div_nonneg
    (mul_nonneg (hR x) (Real.exp_nonneg _)) hZ.le
  have hs' : ∀ x, 0 < P x → 0 < R' x := fun x hx => div_pos
    (mul_pos (hs x hx) (Real.exp_pos _)) hZ
  have hRsum : ∑ x, R' x = 1 := by
    simp only [R', ← Finset.sum_div, Z, div_self hZ.ne']
  have hdiv := divergence_nonneg P R' hP hR' hPsum hRsum hs'
  have he : divergence P R' = divergence P R - (∑ x, P x * g x) + Real.log Z := by
    have hterm (x : X) : P x * Real.log (P x / R' x) =
        P x * Real.log (P x / R x) - P x * g x + P x * Real.log Z := by
      rcases eq_or_lt_of_le (hP x) with hx | hx
      · simp [← hx]
      · have hr := hs x hx
        simp only [R', Real.log_div hx.ne' (ne_of_gt (hs' x hx)),
          Real.log_div (mul_pos hr (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp,
          Real.log_div hx.ne' hr.ne']
        ring
    simp only [divergence, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hPsum, one_mul]
  rw [he] at hdiv
  linarith

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

noncomputable def binaryDivergence (r p : ℝ) : ℝ :=
  r * Real.log (r / p) + (1-r) * Real.log ((1-r)/(1-p))

lemma mul_log_div_le {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) :
    r * Real.log (r/p) ≤ r * (r/p - 1) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp
  · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hr hp)) hr.le

theorem binaryDivergence_upper {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Icc 0 1) :
    binaryDivergence r p ≤ (r-p)^2 / (p*(1-p)) := by
  have hq : 0 < 1-p := sub_pos.mpr hp.2
  have h1 := mul_log_div_le hr.1 hp.1
  have h2 := mul_log_div_le (sub_nonneg.mpr hr.2) hq
  have he : r * (r/p-1) + (1-r)*((1-r)/(1-p)-1) = (r-p)^2/(p*(1-p)) := by
    field_simp [hp.1.ne', hq.ne']
    ring
  exact (add_le_add h1 h2).trans_eq he

lemma mul_log_div_eq {r p : ℝ} (hp : p ≠ 0) :
    r * Real.log (r / p) = r * Real.log r - r * Real.log p := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [Real.log_div hr hp]
    ring

noncomputable def binaryRemainder (p r : ℝ) : ℝ :=
  r * Real.log r + (1-r) * Real.log (1-r) -
    r * Real.log p - (1-r)*Real.log (1-p) - 2*(r-p)^2

lemma continuous_binaryRemainder (p : ℝ) : Continuous (binaryRemainder p) := by
  unfold binaryRemainder
  fun_prop

lemma binaryRemainder_eq {p : ℝ} (hp : p ∈ Ioo 0 1) (r : ℝ) :
    binaryRemainder p r = binaryDivergence r p - 2*(r-p)^2 := by
  unfold binaryRemainder binaryDivergence
  rw [mul_log_div_eq hp.1.ne', mul_log_div_eq (sub_pos.mpr hp.2).ne']
  ring

lemma hasDerivAt_binaryRemainder (p : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt (binaryRemainder p)
      (Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p)) r := by
  have hid := hasDerivAt_id r
  have ho := (hasDerivAt_const r (1:ℝ)).sub hid
  have hmul := (Real.hasDerivAt_mul_log hr.1.ne').add
    ((Real.hasDerivAt_mul_log (sub_pos.mpr hr.2).ne').comp r ho)
  convert ((hmul.sub (hid.mul_const (Real.log p))).sub
    (ho.mul_const (Real.log (1-p)))).sub
      (((hid.sub_const p).pow 2).const_mul 2) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

lemma hasDerivAt_binaryRemainder_deriv (p : ℝ) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt
      (fun r => Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p))
      (r⁻¹ + (1-r)⁻¹ - 4) r := by
  have hid := hasDerivAt_id r
  have ho := (hasDerivAt_const r (1:ℝ)).sub hid
  convert (((((Real.hasDerivAt_log hr.1.ne').sub
    ((Real.hasDerivAt_log (sub_pos.mpr hr.2).ne').comp r ho)).sub_const
      (Real.log p)).add_const (Real.log (1-p))).sub
        ((hid.sub_const p).const_mul 4)) using 1 <;> first | rfl | ring

lemma binary_second_deriv_nonneg {r : ℝ} (hr : r ∈ Ioo 0 1) :
    0 ≤ r⁻¹ + (1-r)⁻¹ - 4 := by
  have hq : 0 < 1-r := sub_pos.mpr hr.2
  have he : r⁻¹ + (1-r)⁻¹ - 4 = (2*r-1)^2 / (r*(1-r)) := by
    field_simp [hr.1.ne', hq.ne']
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) (mul_pos hr.1 hq).le

lemma convexOn_binaryRemainder (p : ℝ) : ConvexOn ℝ (Icc 0 1) (binaryRemainder p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0:ℝ) 1)
    (continuous_binaryRemainder p).continuousOn
    (f' := fun r => Real.log r - Real.log (1-r) - Real.log p + Real.log (1-p) - 4*(r-p))
    (f'' := fun r => r⁻¹ + (1-r)⁻¹ - 4)
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_binaryRemainder p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_binaryRemainder_deriv p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact binary_second_deriv_nonneg hr

theorem binaryDivergence_lower {p r : ℝ} (hp : p ∈ Ioo 0 1) (hr : r ∈ Icc 0 1) :
    2*(r-p)^2 ≤ binaryDivergence r p := by
  have hconv := convexOn_binaryRemainder p
  have hder : HasDerivAt (binaryRemainder p) 0 p := by
    simpa using hasDerivAt_binaryRemainder p hp
  have hmin : binaryRemainder p p ≤ binaryRemainder p r := by
    rcases lt_trichotomy p r with h | rfl | h
    · have hs := hconv.le_slope_of_hasDerivAt ⟨hp.1.le, hp.2.le⟩ hr h hder
      rw [slope_def_field] at hs
      have ht := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      simpa using ht
    · rfl
    · have hs := hconv.slope_le_of_hasDerivAt hr ⟨hp.1.le, hp.2.le⟩ h hder
      rw [slope_def_field] at hs
      have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  rw [binaryRemainder_eq hp, binaryRemainder_eq hp] at hmin
  have hz : binaryDivergence p p = 0 := by
    simp [binaryDivergence, hp.1.ne', (sub_pos.mpr hp.2).ne']
  rw [hz] at hmin
  nlinarith

end CriticalPercolation.FiniteEntropy

end
end

end OAI
