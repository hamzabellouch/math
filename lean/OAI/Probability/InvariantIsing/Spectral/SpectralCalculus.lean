import OAI.Probability.InvariantIsing.Spectral.SpectralExistence
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-!
Differentiation of the finite spectral inverse. The inverse function
theorem is applied to the already constructed inverse; no regularity of
that inverse is assumed.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- Third resolvent moment. -/
def finiteThirdResolvent (ρ eig : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ a, ρ a / (b - eig a) ^ 3

theorem finiteSecondResolvent_pos {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) :
    0 < finiteSecondResolvent ρ eig b := by
  obtain ⟨a, ha⟩ := exists_pos_spectral_weight hρ hρsum
  unfold finiteSecondResolvent
  exact Finset.sum_pos' (fun a _ => div_nonneg (hρ a) (sq_nonneg _))
    ⟨a, Finset.mem_univ a, div_pos ha (sq_pos_of_pos (sub_pos.mpr (hb a)))⟩

/-- The Cauchy–Schwarz inequality used for convexity of `x ↦ x R(t x)`. -/
theorem finiteSecondResolvent_sq_le_first_mul_third {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hb : ∀ a, eig a < b) :
    finiteSecondResolvent ρ eig b ^ 2 ≤
      finiteResolvent ρ eig b * finiteThirdResolvent ρ eig b := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro a _
    exact div_nonneg (hρ a) (sub_pos.mpr (hb a)).le
  · intro a _
    exact div_nonneg (hρ a) (pow_nonneg (sub_pos.mpr (hb a)).le 3)
  · intro a _
    apply le_of_eq
    field_simp [ne_of_gt (sub_pos.mpr (hb a))]

theorem hasStrictDerivAt_finiteResolvent (ρ eig : ι → ℝ) {b : ℝ}
    (hb : ∀ a, eig a < b) :
    HasStrictDerivAt (finiteResolvent ρ eig) (-finiteSecondResolvent ρ eig b) b := by
  have hterm : ∀ a, HasStrictDerivAt (fun z : ℝ => ρ a / (z - eig a))
      (-ρ a / (b - eig a) ^ 2) b := by
    intro a
    simpa only [id_eq, zero_mul, mul_one, zero_sub] using
      (hasStrictDerivAt_const b (ρ a)).fun_div
        ((hasStrictDerivAt_id b).sub_const (eig a)) (ne_of_gt (sub_pos.mpr (hb a)))
  convert! HasStrictDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a) using 1
  simp only [finiteSecondResolvent, neg_div, Finset.sum_neg_distrib]

theorem hasStrictDerivAt_finiteSecondResolvent (ρ eig : ι → ℝ) {b : ℝ}
    (hb : ∀ a, eig a < b) :
    HasStrictDerivAt (finiteSecondResolvent ρ eig) (-2 * finiteThirdResolvent ρ eig b) b := by
  have hterm : ∀ a, HasStrictDerivAt (fun z : ℝ => ρ a / (z - eig a) ^ 2)
      (-2 * (ρ a / (b - eig a) ^ 3)) b := by
    intro a
    have hd : HasStrictDerivAt (fun z : ℝ => z - eig a) 1 b := by
      convert! (hasStrictDerivAt_id b).sub_const (eig a) using 1
    convert (hasStrictDerivAt_const b (ρ a)).fun_div
      (hd.fun_pow 2)
      (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr (hb a)))) using 1
    field_simp [ne_of_gt (sub_pos.mpr (hb a))]
    ring
  convert! HasStrictDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a) using 1
  simp only [finiteThirdResolvent, Finset.mul_sum]

/-- Inverse transform for a finite alphabet with positive masses.
The value outside positive arguments is irrelevant to the application. -/
def finiteInverse (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  if hx : 0 < x then (exists_unique_finiteResolvent_of_pos (eig := eig) hρ hρsum hx).choose else 0

theorem finiteInverse_spec (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    (∀ a, eig a < finiteInverse ρ eig hρ hρsum x) ∧
      finiteResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) = x := by
  simp only [finiteInverse, dite_eq_left hx]
  exact (exists_unique_finiteResolvent_of_pos (eig := eig) hρ hρsum hx).choose_spec.1

theorem finiteInverse_left (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {b : ℝ} (hb : ∀ a, eig a < b) :
    finiteInverse ρ eig hρ hρsum (finiteResolvent ρ eig b) = b := by
  have hx := finiteResolvent_pos (fun a => (hρ a).le) hρsum hb
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  exact finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs.1 hb hs.2 rfl

/-- The exact inverse derivative appearing in the finite-spectrum calculation. -/
theorem hasStrictDerivAt_finiteInverse (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (finiteInverse ρ eig hρ hρsum)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
  let b := finiteInverse ρ eig hρ hρsum x
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteResolvent ρ eig hs.1
  have hnear : ∀ᶠ z : ℝ in 𝓝 b, ∀ a, eig a < z := by
    apply Filter.eventually_all.mpr
    intro a
    exact Ioi_mem_nhds (hs.1 a)
  have hinv : ∀ᶠ z : ℝ in 𝓝 b,
      finiteInverse ρ eig hρ hρsum (finiteResolvent ρ eig z) = z := by
    filter_upwards [hnear] with z hz
    exact finiteInverse_left ρ eig hρ hρsum hz
  have hi := hd.to_local_left_inverse (neg_ne_zero.mpr hpos.ne') hinv
  rw [hs.2] at hi
  simpa only [inv_neg, one_div, neg_div] using hi

/-- Finite-alphabet `R`-transform, with its prescribed value at zero. -/
def finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  if 0 < x then finiteInverse ρ eig hρ hρsum x - 1 / x else ∑ a, ρ a * eig a

theorem hasStrictDerivAt_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (finiteR ρ eig hρ hρsum)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) + 1 / x ^ 2) x := by
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hi : HasStrictDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa using (hasStrictDerivAt_const x (1 : ℝ)).fun_div
      (hasStrictDerivAt_id x) (ne_of_gt hx)
  have h := hb.fun_sub hi
  have heq : finiteR ρ eig hρ hρsum =ᶠ[𝓝 x]
      fun y => finiteInverse ρ eig hρ hρsum y - 1 / y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [finiteR, ite_eq_left (show 0 < y from hy)]
  convert h.congr_of_eventuallyEq heq.symm using 1
  ring

theorem finiteR_derivative_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ -1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) + 1 / x ^ 2 := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hsecond := finiteResolvent_sq_le_second (fun a => (hρ a).le) hρsum
    (eig := eig) (b := finiteInverse ρ eig hρ hρsum x)
  rw [hs.2] at hsecond
  have h := one_div_le_one_div_of_le (sq_pos_of_pos hx) hsecond
  simp only [neg_div]
  linarith

theorem hasStrictDerivAt_finiteInverseDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt
      (fun y => -1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum y))
      (2 * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hm := (hasStrictDerivAt_finiteSecondResolvent ρ eig hs.1).comp x hb
  convert (hasStrictDerivAt_const x (-1 : ℝ)).fun_div hm hpos.ne' using 1
  · rfl
  · simp only [Function.comp_apply]
    field_simp [hpos.ne']
    ring

/-- First derivative of `x R(x)`, in a form without cancellation at zero. -/
def finiteEnergyDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  finiteInverse ρ eig hρ hρsum x +
    x * (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x))

theorem hasStrictDerivAt_mul_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteEnergyDerivative ρ eig hρ hρsum x) x := by
  have hr := hasStrictDerivAt_finiteR ρ eig hρ hρsum hx
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  convert (hasStrictDerivAt_id x).fun_mul hr using 1
  · rfl
  · simp only [id_eq, finiteR, ite_eq_left hx, finiteEnergyDerivative]
    field_simp [ne_of_gt hx, hpos.ne']
    ring

/-- The second derivative used in manuscript `up:energy`. -/
theorem hasStrictDerivAt_finiteEnergyDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (finiteEnergyDerivative ρ eig hρ hρsum)
      (2 * (x * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) -
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 2) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3) x := by
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hbp := hasStrictDerivAt_finiteInverseDerivative ρ eig hρ hρsum hx
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  convert hb.fun_add ((hasStrictDerivAt_id x).fun_mul hbp) using 1
  · rfl
  · simp only [id_eq]
    field_simp [hpos.ne']
    ring

theorem finiteEnergy_secondDerivative_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ 2 * (x * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) -
      finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 2) /
      finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3 := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hcs := finiteSecondResolvent_sq_le_first_mul_third (fun a => (hρ a).le) hs.1
  rw [hs.2] at hcs
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hcs)) (pow_nonneg hm.le 3)

end InvariantIsing

end

end OAI
