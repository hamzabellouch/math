import Mathlib

namespace OAI

/-! Numerical character, discriminant and fixed-branch wall-transport inequalities. -/

noncomputable section

namespace PrescribedCharges.Numerical

@[ext] structure Character where
  r : ℝ
  d : ℝ
  w : ℝ
  z : ℝ

namespace Character

def twist (v : Character) (b : ℝ) : Character where
  r := v.r
  d := v.d - b * v.r
  w := v.w - b * v.d + b ^ 2 * v.r / 2
  z := v.z - b * v.w + b ^ 2 * v.d / 2 - b ^ 3 * v.r / 6

def discr (v : Character) : ℝ := v.d ^ 2 - 2 * v.r * v.w

def numerator (v : Character) (a : ℝ) : ℝ := v.w - a ^ 2 * v.r / 2

def defect (v : Character) (a : ℝ) : ℝ := v.z - a ^ 2 * v.d / 6

@[simp] theorem twist_zero (v : Character) : v.twist 0 = v := by
  ext <;> simp [twist]

@[simp] theorem twist_twist (v : Character) (b c : ℝ) :
    (v.twist b).twist c = v.twist (b + c) := by
  ext <;> simp only [twist] <;> ring

@[simp] theorem discr_twist (v : Character) (b : ℝ) :
    (v.twist b).discr = v.discr := by
  simp only [discr, twist]
  ring

theorem discr_at_zero (v : Character) (a : ℝ) (hz : v.numerator a = 0) :
    v.discr = v.d ^ 2 - a ^ 2 * v.r ^ 2 := by
  unfold numerator at hz
  unfold discr
  rw [sub_eq_zero.mp hz]
  ring

theorem rank_bound (v : Character) {a : ℝ} (ha : 0 < a) (hd : 0 < v.d)
    (hz : v.numerator a = 0) (hΔ : 0 ≤ v.discr) : a * |v.r| ≤ v.d := by
  rw [v.discr_at_zero a hz] at hΔ
  have hs : (a * |v.r|) ^ 2 ≤ v.d ^ 2 := by
    simpa only [mul_pow, sq_abs] using (sub_nonneg.mp hΔ)
  have hn : 0 ≤ a * |v.r| := mul_nonneg ha.le (abs_nonneg _)
  nlinarith

theorem hasDerivAt_twist_z (v : Character) (b : ℝ) :
    HasDerivAt (fun t : ℝ => (v.twist t).z) (-(v.twist b).w) b := by
  have h := (((hasDerivAt_const b v.z).sub
    ((hasDerivAt_id b).mul_const v.w)).add
    ((((hasDerivAt_id b).pow 2).mul_const v.d).div_const 2)).sub
    ((((hasDerivAt_id b).pow 3).mul_const v.r).div_const 6)
  apply h.congr_deriv
  dsimp [twist]
  ring

end Character

def comparison (a d r : ℝ) : ℝ := d - a ^ 2 * r ^ 2 / d

def excess (a d r : ℝ) : ℝ := d - a * |r|

theorem comparison_eq_discr_div (v : Character) (a : ℝ) (hd : v.d ≠ 0)
    (hz : v.numerator a = 0) : comparison a v.d v.r = v.discr / v.d := by
  rw [v.discr_at_zero a hz]
  unfold comparison
  field_simp

theorem comparison_factorization (a d r : ℝ) (hd : d ≠ 0) :
    comparison a d r = excess a d r * (d + a * |r|) / d := by
  unfold comparison excess
  field_simp
  nlinarith [sq_abs r]

theorem comparison_sub_excess (a d r : ℝ) (hd : d ≠ 0) :
    comparison a d r - excess a d r = a * |r| * excess a d r / d := by
  rw [comparison_factorization a d r hd]
  field_simp
  ring

theorem two_excess_sub_comparison (a d r : ℝ) (hd : d ≠ 0) :
    2 * excess a d r - comparison a d r = excess a d r ^ 2 / d := by
  rw [comparison_factorization a d r hd]
  unfold excess
  field_simp
  ring

theorem comparison_bounds {a d r : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hr : a * |r| ≤ d) :
    0 ≤ comparison a d r ∧ comparison a d r ≤ d ∧
      excess a d r ≤ comparison a d r ∧ comparison a d r ≤ 2 * excess a d r := by
  have he : 0 ≤ excess a d r := sub_nonneg.mpr hr
  have hl : excess a d r ≤ comparison a d r := by
    have h := div_nonneg (mul_nonneg (mul_nonneg ha.le (abs_nonneg r)) he) hd.le
    rw [← comparison_sub_excess a d r hd.ne'] at h
    exact sub_nonneg.mp h
  have hu : comparison a d r ≤ 2 * excess a d r := by
    have h := div_nonneg (sq_nonneg (excess a d r)) hd.le
    rw [← two_excess_sub_comparison a d r hd.ne'] at h
    exact sub_nonneg.mp h
  refine ⟨he.trans hl, ?_, hl, hu⟩
  exact sub_le_self d (div_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg r)) hd.le)

theorem excess_estimate_to_comparison {a C d r D : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hd : 0 < d) (hr : a * |r| ≤ d)
    (hD : D ≤ C * excess a d r) : D ≤ C * comparison a d r := by
  exact hD.trans (mul_le_mul_of_nonneg_left (comparison_bounds ha hd hr).2.2.1 hC)

theorem comparison_add_gap (a d₁ d₂ r₁ r₂ : ℝ)
    (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₁₂ : d₁ + d₂ ≠ 0) :
    comparison a (d₁ + d₂) (r₁ + r₂) -
      (comparison a d₁ r₁ + comparison a d₂ r₂) =
      a ^ 2 * (r₁ * d₂ - r₂ * d₁) ^ 2 / (d₁ * d₂ * (d₁ + d₂)) := by
  unfold comparison
  field_simp
  ring

theorem comparison_superadditive (a r₁ r₂ : ℝ) {d₁ d₂ : ℝ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    comparison a d₁ r₁ + comparison a d₂ r₂ ≤
      comparison a (d₁ + d₂) (r₁ + r₂) := by
  have h := div_nonneg
    (mul_nonneg (sq_nonneg a) (sq_nonneg (r₁ * d₂ - r₂ * d₁)))
    (mul_nonneg (mul_nonneg h₁.le h₂.le) (add_nonneg h₁.le h₂.le))
  rw [← comparison_add_gap a d₁ d₂ r₁ r₂ h₁.ne' h₂.ne' (add_pos h₁ h₂).ne'] at h
  exact sub_nonneg.mp h

theorem sum_comparison_le {ι : Type*} (s : Finset ι) (a : ℝ) (d r : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) :
    ∑ i ∈ s, comparison a (d i) (r i) ≤
      comparison a (∑ i ∈ s, d i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comparison]
  | @insert i s hi ih =>
    have hdi : 0 < d i := hd i (Finset.mem_insert_self _ _)
    have hds : ∀ j ∈ s, 0 < d j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    by_cases hs : s.Nonempty
    · have hsum : 0 < ∑ j ∈ s, d j := Finset.sum_pos hds hs
      exact (add_le_add (le_refl _) (ih hds)).trans
        (comparison_superadditive a (r i) (∑ j ∈ s, r j) hdi hsum)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [he, comparison]

theorem exists_violating_factor {ι : Type*} (s : Finset ι) (a k : ℝ)
    (d r D : ι → ℝ) (hd : ∀ i ∈ s, 0 < d i) (hk : 0 ≤ k)
    (h : k * comparison a (∑ i ∈ s, d i) (∑ i ∈ s, r i) < ∑ i ∈ s, D i) :
    ∃ i ∈ s, k * comparison a (d i) (r i) < D i := by
  by_contra hn
  push Not at hn
  have hf := Finset.sum_le_sum hn
  have hs := mul_le_mul_of_nonneg_left (sum_comparison_le s a d r hd) hk
  rw [Finset.mul_sum] at hs
  linarith

theorem discriminant_split_two (a d₁ d₂ r₁ r₂ : ℝ) :
    (d₁ + d₂) ^ 2 - a ^ 2 * (r₁ + r₂) ^ 2 =
      (d₁ ^ 2 - a ^ 2 * r₁ ^ 2) + (d₂ ^ 2 - a ^ 2 * r₂ ^ 2) +
        2 * (d₁ * d₂ - a ^ 2 * r₁ * r₂) := by ring

theorem cross_term_nonneg {a d₁ d₂ r₁ r₂ : ℝ} (ha : 0 ≤ a)
    (h₁ : a * |r₁| ≤ d₁) (h₂ : a * |r₂| ≤ d₂) :
    0 ≤ d₁ * d₂ - a ^ 2 * r₁ * r₂ := by
  have hn₁ := mul_nonneg ha (abs_nonneg r₁)
  have hn₂ := mul_nonneg ha (abs_nonneg r₂)
  have hp := mul_le_mul h₁ h₂ hn₂ (hn₁.trans h₁)
  have habs : r₁ * r₂ ≤ |r₁| * |r₂| := by
    simpa only [abs_mul] using le_abs_self (r₁ * r₂)
  have h := mul_le_mul_of_nonneg_left habs (sq_nonneg a)
  nlinarith

theorem cross_term_zero {a d₁ d₂ r₁ r₂ : ℝ}
    (ha : 0 < a) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h₁ : a * |r₁| ≤ d₁) (h₂ : a * |r₂| ≤ d₂)
    (hz : d₁ * d₂ - a ^ 2 * r₁ * r₂ = 0) :
    d₁ = a * |r₁| ∧ d₂ = a * |r₂| ∧ 0 < r₁ * r₂ := by
  have hn₁ := mul_nonneg ha.le (abs_nonneg r₁)
  have hn₂ := mul_nonneg ha.le (abs_nonneg r₂)
  have habs : r₁ * r₂ ≤ |r₁| * |r₂| := by
    simpa only [abs_mul] using le_abs_self (r₁ * r₂)
  have hp : d₁ * d₂ ≤ (a * |r₁|) * (a * |r₂|) := by
    nlinarith [mul_le_mul_of_nonneg_left habs (sq_nonneg a)]
  have he₁ : d₁ = a * |r₁| :=
    le_antisymm ((mul_le_mul_iff_left₀ hd₂).mp
      (hp.trans (mul_le_mul_of_nonneg_left h₂ hn₁))) h₁
  have he₂ : d₂ = a * |r₂| := by
    apply le_antisymm _ h₂
    rw [← he₁] at hp
    exact (mul_le_mul_iff_right₀ hd₁).mp hp
  refine ⟨he₁, he₂, ?_⟩
  have hprod : 0 < a ^ 2 * (r₁ * r₂) := by nlinarith [mul_pos hd₁ hd₂]
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.2
  · exact False.elim ((sq_nonneg a).not_gt h.1)

theorem discriminant_strict_drop {a d₁ d₂ r₁ r₂ : ℝ}
    (hΔ₁ : 0 ≤ d₁ ^ 2 - a ^ 2 * r₁ ^ 2)
    (hΔ₂ : 0 ≤ d₂ ^ 2 - a ^ 2 * r₂ ^ 2)
    (hc : 0 < d₁ * d₂ - a ^ 2 * r₁ * r₂) :
    d₁ ^ 2 - a ^ 2 * r₁ ^ 2 < (d₁ + d₂) ^ 2 - a ^ 2 * (r₁ + r₂) ^ 2 ∧
    d₂ ^ 2 - a ^ 2 * r₂ ^ 2 < (d₁ + d₂) ^ 2 - a ^ 2 * (r₁ + r₂) ^ 2 := by
  rw [discriminant_split_two]
  constructor <;> linarith

theorem no_infinite_discrete_descent {N : ℕ} (hN : 0 < N) :
    ¬ ∃ δ : ℕ → ℝ, (∀ i, 0 ≤ δ i) ∧
      (∀ i, ∃ m : ℤ, δ i = (m : ℝ) / (N : ℝ)) ∧ (∀ i, δ (i + 1) < δ i) := by
  classical
  rintro ⟨δ, hpos, hlattice, hlt⟩
  choose m hm using hlattice
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmpos (i : ℕ) : 0 ≤ m i := by
    have h := hpos i
    rw [hm i] at h
    have h' : (0 : ℝ) ≤ (m i : ℝ) := by simpa only [zero_mul] using (le_div_iff₀ hn).mp h
    exact_mod_cast h'
  have hmstep (i : ℕ) : m (i + 1) + 1 ≤ m i := by
    have h := hlt i
    rw [hm i, hm (i + 1), div_lt_div_iff_of_pos_right hn] at h
    exact Int.add_one_le_iff.mpr (Int.cast_lt.mp h)
  have hmbound (i : ℕ) : m i + (i : ℤ) ≤ m 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      push_cast
      linarith [hmstep i]
  obtain ⟨n, hn'⟩ := exists_nat_gt (m 0)
  have hb := hmbound n
  have hp := hmpos n
  linarith

namespace Character

def branchD (v : Character) (a : ℝ) : ℝ := Real.sqrt (v.discr + a ^ 2 * v.r ^ 2)

def branchB (v : Character) (a : ℝ) : ℝ := (v.d - v.branchD a) / v.r

def branchDefect (v : Character) (a : ℝ) : ℝ :=
  (v.twist (v.branchB a)).defect a

def branchComparison (v : Character) (a : ℝ) : ℝ := comparison a (v.branchD a) v.r

theorem branch_radicand_pos (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    0 < v.discr + a ^ 2 * v.r ^ 2 :=
  add_pos_of_nonneg_of_pos hΔ (mul_pos (sq_pos_of_pos ha) (sq_pos_of_ne_zero hr))

theorem branchD_pos (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) : 0 < v.branchD a :=
  Real.sqrt_pos.mpr (v.branch_radicand_pos ha hr hΔ)

theorem branchD_sq (v : Character) (a : ℝ) (hΔ : 0 ≤ v.discr) :
    v.branchD a ^ 2 = v.discr + a ^ 2 * v.r ^ 2 :=
  Real.sq_sqrt (add_nonneg hΔ (mul_nonneg (sq_nonneg a) (sq_nonneg v.r)))

theorem twist_branchB_d (v : Character) (a : ℝ) (hr : v.r ≠ 0) :
    (v.twist (v.branchB a)).d = v.branchD a := by
  dsimp [twist, branchB]
  field_simp
  ring

theorem numerator_branch (v : Character) (a : ℝ) (hr : v.r ≠ 0)
    (hΔ : 0 ≤ v.discr) : (v.twist (v.branchB a)).numerator a = 0 := by
  have hi := v.discr_twist (v.branchB a)
  unfold discr at hi
  rw [v.twist_branchB_d a hr] at hi
  change v.branchD a ^ 2 - 2 * v.r * (v.twist (v.branchB a)).w = _ at hi
  have hs := v.branchD_sq a hΔ
  unfold discr at hs
  have hmul : v.r * (v.twist (v.branchB a)).numerator a = 0 := by
    change v.r * ((v.twist (v.branchB a)).w - a ^ 2 * v.r / 2) = 0
    nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left hr

theorem branchComparison_nonneg (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    0 ≤ v.branchComparison a := by
  have hd := v.branchD_pos ha hr hΔ
  have hb : a * |v.r| ≤ v.branchD a := by
    have hs := v.branchD_sq a hΔ
    nlinarith [sq_abs v.r]
  exact (comparison_bounds ha hd hb).1

theorem branch_rate_le (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    a * v.r ^ 2 / v.branchD a ^ 2 ≤ 1 / a := by
  have hd := v.branchD_pos ha hr hΔ
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) ha).2
  rw [one_mul, v.branchD_sq a hΔ]
  nlinarith

theorem hasDerivAt_branchD (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    HasDerivAt v.branchD (a * v.r ^ 2 / v.branchD a) a := by
  have h := ((hasDerivAt_const a v.discr).add
    (((hasDerivAt_id a).pow 2).mul_const (v.r ^ 2))).sqrt
    (v.branch_radicand_pos ha hr hΔ).ne'
  apply h.congr_deriv
  dsimp [branchD]
  ring

theorem hasDerivAt_branchB (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    HasDerivAt v.branchB (-a * v.r / v.branchD a) a := by
  have h := ((hasDerivAt_const a v.d).sub
    (v.hasDerivAt_branchD ha hr hΔ)).div_const v.r
  apply h.congr_deriv
  field_simp
  ring

theorem hasDerivAt_branchDefect (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    HasDerivAt v.branchDefect (-a / 3 * v.branchComparison a) a := by
  have hd := v.hasDerivAt_branchD ha hr hΔ
  have hz := (v.hasDerivAt_twist_z (v.branchB a)).comp a
    (v.hasDerivAt_branchB ha hr hΔ)
  have h := hz.sub ((((hasDerivAt_id a).pow 2).mul hd).div_const 6)
  have hw := v.numerator_branch a hr hΔ
  change (v.twist (v.branchB a)).w - a ^ 2 * v.r / 2 = 0 at hw
  unfold branchDefect defect
  simp only [v.twist_branchB_d _ hr]
  apply h.congr_deriv
  rw [sub_eq_zero.mp hw]
  dsimp [branchComparison, comparison]
  ring

theorem hasDerivAt_branchComparison (v : Character) {a : ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) :
    HasDerivAt v.branchComparison
      (-(a * v.r ^ 2 / v.branchD a ^ 2) * v.branchComparison a) a := by
  have hd := v.hasDerivAt_branchD ha hr hΔ
  have h := hd.sub ((((hasDerivAt_id a).pow 2).mul_const (v.r ^ 2)).div hd
    (v.branchD_pos ha hr hΔ).ne')
  apply h.congr_deriv
  dsimp [branchComparison, comparison]
  field_simp
  ring

theorem hasDerivAt_branch_difference (v : Character) {a k' : ℝ} {k : ℝ → ℝ}
    (ha : 0 < a) (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) (hk : HasDerivAt k k' a) :
    HasDerivAt (fun t => v.branchDefect t - k t * v.branchComparison t)
      (v.branchComparison a *
        (-a / 3 - k' + k a * (a * v.r ^ 2 / v.branchD a ^ 2))) a := by
  apply ((v.hasDerivAt_branchDefect ha hr hΔ).sub
    (hk.mul (v.hasDerivAt_branchComparison ha hr hΔ))).congr_deriv
  ring

theorem hasDerivAt_defect_rank_zero (v : Character) (a : ℝ) (hr : v.r = 0) :
    HasDerivAt v.defect (-a / 3 * comparison a v.d v.r) a := by
  have h := (hasDerivAt_const a v.z).sub
    ((((hasDerivAt_id a).pow 2).mul_const v.d).div_const 6)
  apply h.congr_deriv
  simp [comparison, hr]
  ring

theorem hasDerivAt_comparison_rank_zero (v : Character) (a : ℝ) (hr : v.r = 0) :
    HasDerivAt (fun t : ℝ => comparison t v.d v.r) 0 a := by
  simpa [comparison, hr] using hasDerivAt_const a v.d

end Character

def belowCoefficient (A C a : ℝ) : ℝ := C + (A ^ 2 - a ^ 2) / 6

def tailCoefficient (R a : ℝ) : ℝ := a * (R - a) / 3

def aboveCoefficient (A C a : ℝ) : ℝ := C * a / A

theorem hasDerivAt_belowCoefficient (A C a : ℝ) :
    HasDerivAt (belowCoefficient A C) (-a / 3) a := by
  apply ((hasDerivAt_const a C).add
    (((hasDerivAt_const a (A ^ 2)).sub ((hasDerivAt_id a).pow 2)).div_const 6)).congr_deriv
  dsimp
  ring

theorem hasDerivAt_tailCoefficient (R a : ℝ) :
    HasDerivAt (tailCoefficient R) ((R - 2 * a) / 3) a := by
  apply (((hasDerivAt_id a).mul
    ((hasDerivAt_const a R).sub (hasDerivAt_id a))).div_const 3).congr_deriv
  dsimp
  ring

theorem hasDerivAt_aboveCoefficient (A C a : ℝ) :
    HasDerivAt (aboveCoefficient A C) (C / A) a := by
  apply (((hasDerivAt_id a).const_mul C).div_const A).congr_deriv
  ring

theorem belowCoefficient_nonneg {A C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (haA : a ≤ A) : 0 ≤ belowCoefficient A C a := by
  unfold belowCoefficient
  have hsq : a ^ 2 ≤ A ^ 2 := by nlinarith
  positivity

theorem below_derivative_nonneg {A C a d r S : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (haA : a ≤ A) (hS : 0 ≤ S) :
    0 ≤ S * (-a / 3 - (-a / 3) + belowCoefficient A C a * (a * r ^ 2 / d ^ 2)) := by
  simp only [sub_self, zero_add]
  exact mul_nonneg hS (mul_nonneg (belowCoefficient_nonneg hC ha haA)
    (div_nonneg (mul_nonneg ha.le (sq_nonneg _)) (sq_nonneg _)))

theorem tail_derivative_nonpos {R a S rate : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hS : 0 ≤ S) (hRate : rate ≤ 1 / a) :
    S * (-a / 3 - (R - 2 * a) / 3 + tailCoefficient R a * rate) ≤ 0 := by
  have hk : 0 ≤ tailCoefficient R a := by
    exact div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr haR)) (by norm_num)
  have h := mul_le_mul_of_nonneg_left hRate hk
  have heq : -a / 3 - (R - 2 * a) / 3 + tailCoefficient R a * (1 / a) = 0 := by
    unfold tailCoefficient
    field_simp
    ring
  apply mul_nonpos_of_nonneg_of_nonpos hS
  linarith

theorem above_derivative_nonpos {A C a S rate : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (ha : 0 < a) (hS : 0 ≤ S) (hRate : rate ≤ 1 / a) :
    S * (-a / 3 - C / A + aboveCoefficient A C a * rate) ≤ 0 := by
  have hk : 0 ≤ aboveCoefficient A C a :=
    div_nonneg (mul_nonneg hC ha.le) hA.le
  have h := mul_le_mul_of_nonneg_left hRate hk
  have heq : aboveCoefficient A C a * (1 / a) = C / A := by
    unfold aboveCoefficient
    field_simp
  apply mul_nonpos_of_nonneg_of_nonpos hS
  rw [heq] at h
  linarith

private theorem endpoint_le_of_nonneg_derivative {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Set.Icc a b, 0 ≤ f' x) : f a ≤ f b := by
  have hm : MonotoneOn f (Set.Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hn x (interior_subset hx))
  exact hm (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab

private theorem endpoint_le_of_nonpos_derivative {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Set.Icc a b, f' x ≤ 0) : f b ≤ f a := by
  have hm : AntitoneOn f (Set.Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hn x (interior_subset hx))
  exact hm (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab

namespace Character

theorem below_endpoint (v : Character) {A C a : ℝ}
    (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) (hC : 0 ≤ C) (ha : 0 < a) (haA : a ≤ A) :
    v.branchDefect a - belowCoefficient A C a * v.branchComparison a ≤
      v.branchDefect A - C * v.branchComparison A := by
  have h := endpoint_le_of_nonneg_derivative haA
    (f := fun x => v.branchDefect x - belowCoefficient A C x * v.branchComparison x)
    (f' := fun x => v.branchComparison x *
      (-x / 3 - (-x / 3) + belowCoefficient A C x * (x * v.r ^ 2 / v.branchD x ^ 2)))
    (fun x hx => v.hasDerivAt_branch_difference (ha.trans_le hx.1) hr hΔ
      (hasDerivAt_belowCoefficient A C x))
    (fun x hx => below_derivative_nonneg hC (ha.trans_le hx.1) hx.2
      (v.branchComparison_nonneg (ha.trans_le hx.1) hr hΔ))
  simpa only [belowCoefficient, sub_self, zero_div, add_zero] using h

theorem tail_endpoint (v : Character) {A R : ℝ}
    (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) (hA : 0 < A) (hAR : A ≤ R) :
    v.branchDefect R ≤
      v.branchDefect A - tailCoefficient R A * v.branchComparison A := by
  have h := endpoint_le_of_nonpos_derivative hAR
    (f := fun x => v.branchDefect x - tailCoefficient R x * v.branchComparison x)
    (f' := fun x => v.branchComparison x *
      (-x / 3 - (R - 2 * x) / 3 + tailCoefficient R x * (x * v.r ^ 2 / v.branchD x ^ 2)))
    (fun x hx => v.hasDerivAt_branch_difference (hA.trans_le hx.1) hr hΔ
      (hasDerivAt_tailCoefficient R x))
    (fun x hx => tail_derivative_nonpos (hA.trans_le hx.1) hx.2
      (v.branchComparison_nonneg (hA.trans_le hx.1) hr hΔ)
      (v.branch_rate_le (hA.trans_le hx.1) hr hΔ))
  simpa only [tailCoefficient, sub_self, mul_zero, zero_div, zero_mul, sub_zero] using h

theorem above_endpoint (v : Character) {A C a : ℝ}
    (hr : v.r ≠ 0) (hΔ : 0 ≤ v.discr) (hA : 0 < A) (hC : 0 ≤ C) (hAa : A ≤ a) :
    v.branchDefect a - aboveCoefficient A C a * v.branchComparison a ≤
      v.branchDefect A - C * v.branchComparison A := by
  have h := endpoint_le_of_nonpos_derivative hAa
    (f := fun x => v.branchDefect x - aboveCoefficient A C x * v.branchComparison x)
    (f' := fun x => v.branchComparison x *
      (-x / 3 - C / A + aboveCoefficient A C x * (x * v.r ^ 2 / v.branchD x ^ 2)))
    (fun x hx => v.hasDerivAt_branch_difference (hA.trans_le hx.1) hr hΔ
      (hasDerivAt_aboveCoefficient A C x))
    (fun x hx => above_derivative_nonpos hA hC (hA.trans_le hx.1)
      (v.branchComparison_nonneg (hA.trans_le hx.1) hr hΔ)
      (v.branch_rate_le (hA.trans_le hx.1) hr hΔ))
  simpa only [aboveCoefficient, mul_div_cancel_right₀ _ hA.ne'] using h

theorem below_endpoint_rank_zero (v : Character) (A C a : ℝ) (hr : v.r = 0) :
    v.defect a - belowCoefficient A C a * comparison a v.d v.r =
      v.defect A - C * comparison A v.d v.r := by
  simp [defect, belowCoefficient, comparison, hr]
  ring

theorem tail_endpoint_rank_zero (v : Character) (A R : ℝ)
    (hr : v.r = 0) (hd : 0 ≤ v.d) :
    v.defect R ≤ v.defect A - tailCoefficient R A * comparison A v.d v.r := by
  simp only [defect, tailCoefficient, comparison, hr, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_div, sub_zero]
  nlinarith [mul_nonneg (sq_nonneg (R - A)) hd]

theorem above_endpoint_rank_zero (v : Character) {A C a : ℝ}
    (hr : v.r = 0) (hd : 0 ≤ v.d) (hA : 0 < A) (hC : 0 ≤ C) (hAa : A ≤ a) :
    v.defect a - aboveCoefficient A C a * comparison a v.d v.r ≤
      v.defect A - C * comparison A v.d v.r := by
  have hcoef : C ≤ aboveCoefficient A C a := by
    change C ≤ C * a / A
    rw [le_div_iff₀ hA]
    exact mul_le_mul_of_nonneg_left hAa hC
  have hsq : A ^ 2 ≤ a ^ 2 := by nlinarith
  have hdef : v.defect a ≤ v.defect A := by
    unfold defect
    exact sub_le_sub_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hd)
      (by norm_num)) _
  simp only [comparison, hr, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, sub_zero]
  exact sub_le_sub hdef (mul_le_mul_of_nonneg_right hcoef hd)

end Character

def tailThreshold (A C : ℝ) : ℝ := A + 3 * C / A

def globalCorrection (A C : ℝ) : ℝ :=
  max (C + A ^ 2 / 6) (C * tailThreshold A C / A)

theorem tailThreshold_pos {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    0 < tailThreshold A C := by
  unfold tailThreshold
  positivity

theorem apex_le_tailThreshold {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    A ≤ tailThreshold A C := by
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hC) hA.le)

theorem globalCorrection_nonneg {A C : ℝ} (hC : 0 ≤ C) :
    0 ≤ globalCorrection A C := by
  exact (add_nonneg hC (div_nonneg (sq_nonneg A) (by norm_num))).trans (le_max_left _ _)

theorem belowCoefficient_le_globalCorrection (A C a : ℝ) :
    belowCoefficient A C a ≤ globalCorrection A C := by
  unfold belowCoefficient globalCorrection
  exact (show C + (A ^ 2 - a ^ 2) / 6 ≤ C + A ^ 2 / 6 by nlinarith [sq_nonneg a]).trans
    (le_max_left _ _)

theorem aboveCoefficient_le_globalCorrection {A C a : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (ha : a ≤ tailThreshold A C) :
    aboveCoefficient A C a ≤ globalCorrection A C := by
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hC) hA.le).trans
    (le_max_right _ _)

theorem tailCoefficient_at_apex_gt {A C R : ℝ}
    (hA : 0 < A) (hR : tailThreshold A C < R) : C < tailCoefficient R A := by
  have h : 3 * C / A < R - A := by unfold tailThreshold at hR; linarith
  have hp := (div_lt_iff₀ hA).mp h
  unfold tailCoefficient
  nlinarith

theorem exists_nonnegative_rational_ge (K : ℝ) :
    ∃ k : ℚ, 0 ≤ k ∧ K ≤ (k : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt K
  refine ⟨n, Nat.cast_nonneg n, ?_⟩
  simpa only [Rat.cast_natCast] using hn.le

theorem unnormalize_iff {h : ℝ} (hh : 0 < h) (a k z d : ℝ) :
    z / h ≤ (a ^ 2 / 6 + k) * (d / h) ↔ z ≤ (a ^ 2 / 6 + k) * d := by
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hh]

theorem rescale_correction_iff {s : ℝ} (hs : s ≠ 0) (a K z d : ℝ) :
    z ≤ ((a / s) ^ 2 / 6 + K) * (s ^ 2 * d) ↔
      z ≤ (a ^ 2 / 6 + s ^ 2 * K) * d := by
  have h : ((a / s) ^ 2 / 6 + K) * (s ^ 2 * d) = (a ^ 2 / 6 + s ^ 2 * K) * d := by
    field_simp
  rw [h]

theorem rescale_threshold_iff {s : ℝ} (hs : 0 < s) (a R : ℝ) :
    R < a / s ↔ s * R < a := by
  rw [lt_div_iff₀ hs, mul_comm R s]

theorem numerical_conditions_insufficient (a k : ℝ) :
    ∃ v : Character, v.d = 1 ∧ v.r = 0 ∧ v.numerator a = 0 ∧
      0 ≤ v.discr ∧ (a ^ 2 / 6 + k) * v.d < v.z := by
  refine ⟨⟨0, 1, 0, (a ^ 2 / 6 + k) + 1⟩, ?_⟩
  simp [Character.numerator, Character.discr]

end PrescribedCharges.Numerical

end

end OAI
