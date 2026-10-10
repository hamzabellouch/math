import Mathlib

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries

section Field
variable {K : Type*} [Field K]

def elementaryCoeff (q u : K) : ℕ → K
  | 0 => 1
  | n + 1 => u * q ^ n * elementaryCoeff q u n / (1 - q ^ (n + 1))

noncomputable def elementary (q u : K) : PowerSeries K :=
  PowerSeries.mk (elementaryCoeff q u)

@[simp] theorem coeff_elementary (q u : K) (n : ℕ) :
    PowerSeries.coeff n (elementary q u) = elementaryCoeff q u n := by
  simp [elementary]

@[simp] theorem constant_elementary (q u : K) :
    PowerSeries.constantCoeff (elementary q u) = 1 := rfl

theorem elementaryCoeff_product (q u : K) (n : ℕ) :
    elementaryCoeff q u n =
      (u ^ n * q ^ (∑ i ∈ Finset.range n, i)) /
        ∏ i ∈ Finset.range n, (1 - q ^ (i + 1)) := by
  induction n with
  | zero => simp [elementaryCoeff]
  | succ n ih =>
    rw [elementaryCoeff, ih, Finset.sum_range_succ, Finset.prod_range_succ,
      pow_succ, pow_add]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem elementary_tail (q u : K) (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) :
    elementary q u = (1 + PowerSeries.C u * PowerSeries.X) *
      PowerSeries.rescale q (elementary q u) := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff, map_mul, map_add, constantCoeff_one,
      constantCoeff_C, constantCoeff_X, mul_zero, add_zero, one_mul]
    rw [constant_elementary, ← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp [elementaryCoeff]
  | succ n =>
    rw [add_mul, one_mul, map_add]
    simp only [coeff_elementary, coeff_rescale]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_rescale, coeff_elementary, elementaryCoeff]
    field_simp [hq n]
    ring

@[simp] theorem rescale_C (a u : K) :
    PowerSeries.rescale a (PowerSeries.C u) = PowerSeries.C u := by
  ext n
  cases n <;> simp

theorem elementary_head (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) :
    PowerSeries.rescale q⁻¹ (elementary q u) =
      (1 + PowerSeries.C (u * q⁻¹) * PowerSeries.X) * elementary q u := by
  have h := congrArg (PowerSeries.rescale q⁻¹) (elementary_tail q u hq)
  simp only [map_mul, map_add, map_one, rescale_C, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale, mul_inv_cancel₀ hq0, PowerSeries.rescale_one,
    RingHom.id_apply] at h
  rw [← mul_assoc (PowerSeries.C u), ← map_mul] at h
  exact h

theorem elementary_shift (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) (elementary q u) =
      (∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (u * q⁻¹ ^ (i + 1)) * PowerSeries.X)) *
      elementary q u := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← PowerSeries.rescale_rescale, elementary_head q u hq0 hq]
    simp only [map_mul, map_add, map_one, rescale_C, PowerSeries.rescale_X]
    rw [ih]
    rw [Finset.prod_range_succ]
    simp only [pow_succ', map_mul]
    ring

theorem rescale_inv_of_const_one (a : K) (F : PowerSeries K)
    (hF : PowerSeries.constantCoeff F = 1) :
    PowerSeries.rescale a F⁻¹ = (PowerSeries.rescale a F)⁻¹ := by
  have hR : PowerSeries.constantCoeff (PowerSeries.rescale a F) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, hF]
    exact one_ne_zero
  apply (PowerSeries.eq_inv_iff_mul_eq_one hR).2
  rw [← map_mul, PowerSeries.inv_mul_cancel F (by simp [hF]), map_one]

noncomputable def complete (q u : K) : PowerSeries K := (elementary q (-u))⁻¹

theorem complete_shift (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) (complete q u) =
      (elementary q (-u))⁻¹ *
      (∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (-u * q⁻¹ ^ (i + 1)) * PowerSeries.X))⁻¹ := by
  rw [complete, rescale_inv_of_const_one _ _ (constant_elementary _ _),
    elementary_shift q (-u) hq0 hq t, PowerSeries.mul_inv_rev]

theorem elementary_ratio (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) (elementary q u) * (elementary q u)⁻¹ =
      ∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (u * q⁻¹ ^ (i + 1)) * PowerSeries.X) := by
  rw [elementary_shift q u hq0 hq t, mul_assoc,
    PowerSeries.mul_inv_cancel _ (by simp), mul_one]

theorem complete_ratio (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) (complete q u) * elementary q (-u) =
      (∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (-u * q⁻¹ ^ (i + 1)) * PowerSeries.X))⁻¹ := by
  rw [complete_shift q u hq0 hq t]
  rw [mul_right_comm, PowerSeries.inv_mul_cancel _ (by simp), one_mul]

end Field

namespace RationalRay
noncomputable def v : RatFunc ℚ := RatFunc.X
noncomputable def q : RatFunc ℚ := v ^ (-2 : ℤ)
theorem v_nonzero : v ≠ 0 := RatFunc.X_ne_zero

theorem degree_pow (x : RatFunc ℚ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = n * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

theorem q_nonzero : q ≠ 0 := zpow_ne_zero _ v_nonzero

theorem q_degree : q.intDegree = -2 := by
  change (v ^ (-(2 : ℕ) : ℤ)).intDegree = -2
  rw [zpow_neg, zpow_natCast, RatFunc.intDegree_inv, degree_pow v v_nonzero]
  simp [v]

theorem q_not_root_unity (n : ℕ) : 1 - q ^ (n + 1) ≠ 0 := by
  intro h
  have heq := congrArg RatFunc.intDegree (sub_eq_zero.mp h)
  rw [RatFunc.intDegree_one, degree_pow q q_nonzero, q_degree] at heq
  omega

theorem q_pow (n : ℕ) : q ^ n = v ^ (-2 * (n : ℤ)) := by
  rw [q, ← zpow_natCast, ← zpow_mul]

noncomputable def normalized : PowerSeries (RatFunc ℚ) := elementary q v⁻¹

theorem normalized_coefficient (n : ℕ) :
    PowerSeries.coeff n normalized =
      v ^ (-(n : ℤ) ^ 2) /
        ∏ i ∈ Finset.range n, (1 - v ^ (-2 * ((i + 1 : ℕ) : ℤ))) := by
  rw [normalized, coeff_elementary]
  induction n with
  | zero => simp [elementaryCoeff]
  | succ n ih =>
    rw [elementaryCoeff, ih, Finset.prod_range_succ]
    have hn : v⁻¹ * q ^ n * v ^ (-(n : ℤ) ^ 2) =
        v ^ (-((n + 1 : ℕ) : ℤ) ^ 2) := by
      rw [q_pow, ← zpow_neg_one, ← zpow_add₀ v_nonzero, ← zpow_add₀ v_nonzero]
      congr 1
      push_cast
      ring
    rw [q_pow (n + 1)]
    calc
      _ = (v⁻¹ * q ^ n * v ^ (-(n : ℤ) ^ 2)) /
          ((∏ i ∈ Finset.range n, (1 - v ^ (-2 * ((i + 1 : ℕ) : ℤ)))) *
            (1 - v ^ (-2 * ((n + 1 : ℕ) : ℤ)))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hn]

theorem normalized_ratio (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) normalized * normalized⁻¹ =
      ∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (v⁻¹ * q⁻¹ ^ (i + 1)) * PowerSeries.X) :=
  elementary_ratio q v⁻¹ q_nonzero q_not_root_unity t

end RationalRay

namespace PositiveRay
open PowerSeries
noncomputable def vUnit : (RatFunc ℚ)ˣ := Units.mk0 RationalRay.v RationalRay.v_nonzero
noncomputable def eval : LaurentPolynomial ℕ →+* RatFunc ℚ :=
  LaurentPolynomial.eval₂ (Nat.castRingHom _) vUnit

@[simp] theorem eval_T (b : ℤ) : eval (LaurentPolynomial.T b) = RationalRay.v ^ b := by
  simp [eval, vUnit]

def Positive (F : PowerSeries (RatFunc ℚ)) : Prop :=
  ∃ A : PowerSeries (LaurentPolynomial ℕ), PowerSeries.map eval A = F

theorem positive_mul {F G : PowerSeries (RatFunc ℚ)}
    (hF : Positive F) (hG : Positive G) : Positive (F * G) := by
  obtain ⟨A, rfl⟩ := hF
  obtain ⟨B, rfl⟩ := hG
  exact ⟨A * B, map_mul _ _ _⟩

theorem positive_one : Positive 1 := ⟨1, map_one _⟩

theorem positive_E (b : ℤ) :
    Positive (1 + PowerSeries.C (RationalRay.v ^ b) * PowerSeries.X) := by
  refine ⟨1 + PowerSeries.C (LaurentPolynomial.T b) * PowerSeries.X, ?_⟩
  simp

theorem geometric (a : RatFunc ℚ) :
    PowerSeries.rescale a (PowerSeries.mk 1) * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.mk_one_mul_one_sub_eq_one (RatFunc ℚ))
  simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X] using h

theorem positive_H (b : ℤ) :
    Positive (1 - PowerSeries.C (RationalRay.v ^ b) * PowerSeries.X)⁻¹ := by
  refine ⟨PowerSeries.rescale (LaurentPolynomial.T b) (PowerSeries.mk 1), ?_⟩
  have he : PowerSeries.map eval
      (PowerSeries.rescale (LaurentPolynomial.T b) (PowerSeries.mk 1)) =
      PowerSeries.rescale (RationalRay.v ^ b) (PowerSeries.mk 1) := by
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
      Pi.one_apply, mul_one, map_pow, eval_T]
  rw [he]
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 (geometric _)

theorem positive_E_string (t : ℕ) (b : ℕ → ℤ) :
    Positive (∏ i ∈ Finset.range t,
      (1 + PowerSeries.C (RationalRay.v ^ b i) * PowerSeries.X)) := by
  induction t with
  | zero => simpa using positive_one
  | succ t ih =>
    rw [Finset.prod_range_succ]
    exact positive_mul ih (positive_E _)

theorem positive_H_string (t : ℕ) (b : ℕ → ℤ) :
    Positive (∏ i ∈ Finset.range t,
      (1 - PowerSeries.C (RationalRay.v ^ b i) * PowerSeries.X))⁻¹ := by
  induction t with
  | zero => simpa using positive_one
  | succ t ih =>
    rw [Finset.prod_range_succ, PowerSeries.mul_inv_rev]
    exact positive_mul (positive_H _) ih
end PositiveRay

namespace RationalRay

theorem shift_weight (k : ℤ) (j : ℕ) :
    v ^ k * q⁻¹ ^ (j + 1) = v ^ (k + 2 * ((j + 1 : ℕ) : ℤ)) := by
  have h : q⁻¹ ^ (j + 1) = v ^ (2 * ((j + 1 : ℕ) : ℤ)) := by
    rw [inv_pow, q_pow, ← zpow_neg]
    congr 1
  rw [h, ← zpow_add₀ v_nonzero]

theorem elementary_ratio_positive (k : ℤ) (t : ℕ) :
    PositiveRay.Positive (PowerSeries.rescale (q⁻¹ ^ t) (elementary q (v ^ k)) *
      (elementary q (v ^ k))⁻¹) := by
  rw [elementary_ratio q _ q_nonzero q_not_root_unity t]
  simp_rw [shift_weight]
  exact PositiveRay.positive_E_string t _

theorem complete_ratio_positive (k : ℤ) (t : ℕ) :
    PositiveRay.Positive (PowerSeries.rescale (q⁻¹ ^ t) (complete q (v ^ k)) *
      elementary q (-(v ^ k))) := by
  rw [complete_ratio q _ q_nonzero q_not_root_unity t]
  simp_rw [neg_mul, shift_weight, map_neg, neg_mul, ← sub_eq_add_neg]
  exact PositiveRay.positive_H_string t _

end RationalRay

end ElementaryPositivity.WallUnits
end
end

end OAI
