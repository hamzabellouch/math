import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

/-! Polynomial orbit rigidity from the Mason–Stothers theorem. -/
namespace ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

variable {k : Type*} [Field k]

/-- A polynomial of degree at most one has no nonunit square divisor. -/
lemma isUnit_of_square_dvd {n t : k[X]} (hn : n ≠ 0) (hdeg : n.natDegree ≤ 1)
    (ht : t ^ 2 ∣ n) : IsUnit t := by
  have ht0 : t ≠ 0 := by
    intro h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_dvd_iff] at ht
    exact hn ht
  have hb := natDegree_le_of_dvd ht hn
  rw [natDegree_pow] at hb
  have htdeg : t.natDegree = 0 := by omega
  rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree ht0, htdeg]
  rfl

/-- Coprimality of the square and cube terms of an affine-linear orbit sum. -/
lemma orbit_coprime {a d u n : k[X]} (hn : n ≠ 0) (hdeg : n.natDegree ≤ 1)
    (heq : d ^ 2 + a ^ 2 * u ^ 3 = n) : IsCoprime (d ^ 2) (a ^ 2 * u ^ 3) := by
  have hda : IsRelPrime d a := by
    intro t htd hta
    apply isUnit_of_square_dvd hn hdeg
    rw [← heq]
    exact dvd_add (pow_dvd_pow_of_dvd htd 2)
      (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hta 2) _)
  have hdu : IsRelPrime d u := by
    intro t htd htu
    apply isUnit_of_square_dvd hn hdeg
    rw [← heq]
    apply dvd_add (pow_dvd_pow_of_dvd htd 2)
    exact dvd_mul_of_dvd_right
      ((pow_dvd_pow_of_dvd htu 2).trans (pow_dvd_pow u (by decide : 2 ≤ 3))) _
  exact (hda.isCoprime.pow_left.pow_right).mul_right (hdu.isCoprime.pow_left.pow_right)

/-- The polynomial degree bound expressed with radicals. -/
lemma radical_orbit_bound [DecidableEq k] (a d u n : k[X]) :
    (radical (d ^ 2 * (a ^ 2 * u ^ 3) * (-n))).natDegree ≤
    d.natDegree + a.natDegree + u.natDegree + n.natDegree := by
  classical
  have hdvd : radical (d ^ 2 * (a ^ 2 * u ^ 3) * (-n)) ∣
      radical d * (radical a * radical u) * radical n := by
    apply radical_mul_dvd.trans
    apply mul_dvd_mul
    · apply radical_mul_dvd.trans
      apply mul_dvd_mul
      · rw [radical_pow d (by decide : 2 ≠ 0)]
      · apply radical_mul_dvd.trans
        rw [radical_pow a (by decide : 2 ≠ 0), radical_pow u (by decide : 3 ≠ 0)]
    · rw [radical_neg]
  have hb := natDegree_le_of_dvd hdvd
    (mul_ne_zero (mul_ne_zero radical_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero))
      radical_ne_zero)
  rw [natDegree_mul (mul_ne_zero radical_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero))
      radical_ne_zero,
    natDegree_mul radical_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero),
    natDegree_mul radical_ne_zero radical_ne_zero] at hb
  have ha : (radical a).natDegree ≤ a.natDegree := natDegree_radical_le
  have hd : (radical d).natDegree ≤ d.natDegree := natDegree_radical_le
  have hu : (radical u).natDegree ≤ u.natDegree := natDegree_radical_le
  have hn : (radical n).natDegree ≤ n.natDegree := natDegree_radical_le
  omega

/-- A nonsquare obstruction over the coefficient field forces constant polynomial orbits. -/
theorem orbit_constant [CharZero k] {a d u n : k[X]}
    (ha : a ≠ 0) (hd : d ≠ 0) (hu : u ≠ 0) (hn : n ≠ 0)
    (hdeg : n.natDegree ≤ 1) (heq : d ^ 2 + a ^ 2 * u ^ 3 = n)
    (hns : ∀ z : k, z ^ 2 ≠ -(u.coeff 0) ^ 3) :
    a = C (a.coeff 0) ∧ d = C (d.coeff 0) ∧ u = C (u.coeff 0) := by
  classical
  have hdn : d ^ 2 ≠ 0 := pow_ne_zero _ hd
  have haun : a ^ 2 * u ^ 3 ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hu)
  have hp := Polynomial.abc hdn haun (neg_ne_zero.mpr hn)
    (orbit_coprime hn hdeg heq) (by rw [heq]; ring)
  have hda : d.natDegree = a.natDegree ∧ u.natDegree = 0 := by
    rcases hp with hp | hp
    · have hb := radical_orbit_bound a d u n
      have h1 := hp.1.trans hb
      have h2 := hp.2.1.trans hb
      rw [natDegree_pow] at h1
      rw [natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ hu),
        natDegree_pow, natDegree_pow] at h2
      omega
    · have h1 := derivative_eq_zero.mp hp.1
      have h2 := derivative_eq_zero.mp hp.2.1
      rw [natDegree_pow] at h1
      rw [natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ hu),
        natDegree_pow, natDegree_pow] at h2
      omega
  have hd0 : d.natDegree = 0 := by
    by_contra hdpos
    have hlt : n.natDegree < 2 * d.natDegree := by omega
    have hc := congrArg (fun p : k[X] => p.coeff (2 * d.natDegree)) heq
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hlt] at hc
    have hcd : (d ^ 2).coeff (2 * d.natDegree) = d.leadingCoeff ^ 2 := by
      rw [← natDegree_pow d 2, coeff_natDegree, leadingCoeff_pow]
    have hcau : (a ^ 2 * u ^ 3).coeff (2 * d.natDegree) =
        a.leadingCoeff ^ 2 * (u.coeff 0) ^ 3 := by
      have hdegau : (a ^ 2 * u ^ 3).natDegree = 2 * d.natDegree := by
        rw [natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ hu),
          natDegree_pow, natDegree_pow, hda.2, ← hda.1]
        omega
      rw [← hdegau, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
      congr 2
      exact congrArg (fun m : ℕ => u.coeff m) hda.2
    rw [hcd, hcau] at hc
    apply hns (d.leadingCoeff / a.leadingCoeff)
    rw [div_pow, div_eq_iff (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr ha))]
    linear_combination hc
  exact ⟨eq_C_of_natDegree_eq_zero (hda.1.symm.trans hd0),
    eq_C_of_natDegree_eq_zero hd0, eq_C_of_natDegree_eq_zero hda.2⟩

end ComplexCancellation.Rigidity

namespace ComplexCancellation.Rigidity

lemma ratFunc_intDegree_pow {K : Type*} [Field K] {z : RatFunc K}
    (hz : z ≠ 0) (n : ℕ) : (z ^ n).intDegree = (n : ℤ) * z.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hz) hz, ih]
    push_cast
    ring

/-- The cube of the rational parameter is not the negative of a square. -/
theorem ratFunc_X_cube_nonsquare {K : Type*} [Field K] (z : RatFunc K) :
    z ^ 2 ≠ -(RatFunc.X : RatFunc K) ^ 3 := by
  intro hz
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_eq_neg, pow_eq_zero_iff] at hz
    exact RatFunc.X_ne_zero hz
  have he := congrArg RatFunc.intDegree hz
  rw [ratFunc_intDegree_pow hz0, RatFunc.intDegree_neg,
    ratFunc_intDegree_pow RatFunc.X_ne_zero, RatFunc.intDegree_X] at he
  omega

end ComplexCancellation.Rigidity

end

end OAI
