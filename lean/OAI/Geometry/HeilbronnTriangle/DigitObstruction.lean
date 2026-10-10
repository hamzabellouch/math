import Mathlib

namespace OAI


namespace Problem355.DigitEncoding

open Finset

theorem no_small_representative {h τ s x : ℤ}
    (hh : 0 < h) (hτ : 2 * τ < h)
    (hs : 2 * |s| < h) (hsτ : τ < |s|)
    (hx : x ≡ s [ZMOD h]) : τ < |x| := by
  by_contra hn
  have hxτ : |x| ≤ τ := le_of_not_gt hn
  obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hx
  by_cases hm0 : m = 0
  · subst m
    simp only [mul_zero, sub_eq_zero] at hm
    subst s
    omega
  · have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
    have htri : |s - x| ≤ |s| + |x| := abs_sub s x
    rw [hm, abs_mul, abs_of_pos hh] at htri
    have hsmall : 2 * |x| < h :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxτ (by omega)) hτ
    nlinarith only [hsmall, hs, htri, hm1, hh]

theorem partial_sum_bound (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k, 50 * |E i| ≤ 3 * (B - 1)) :
    50 * |∑ i ∈ range k, E i * B ^ i| ≤ 3 * (B ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun i hi => hE i (Nat.lt_succ_of_lt hi))
    have hk := hE k (Nat.lt_succ_self k)
    have hpow : 0 ≤ B ^ k := pow_nonneg (by omega) k
    have htri := abs_add_le (∑ i ∈ range k, E i * B ^ i) (E k * B ^ k)
    rw [abs_mul, abs_of_nonneg hpow] at htri
    rw [sum_range_succ, pow_succ]
    nlinarith

theorem distinguished_digit_bound (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k, 50 * |E i| ≤ 3 * (B - 1))
    (hk : E k ≠ 0) :
    47 * B ^ k + 3 ≤ 50 * |∑ i ∈ range (k + 1), E i * B ^ i| := by
  have hprev := partial_sum_bound B hB E k hE
  have hpow : 0 ≤ B ^ k := pow_nonneg (by omega) k
  have hk1 : 1 ≤ |E k| := Int.one_le_abs hk
  have htri := abs_sub (∑ i ∈ range (k + 1), E i * B ^ i)
    (∑ i ∈ range k, E i * B ^ i)
  rw [sum_range_succ, add_sub_cancel_left, abs_mul, abs_of_nonneg hpow] at htri
  rw [sum_range_succ]
  nlinarith

theorem digit_obstruction (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k + 1, 50 * |E i| ≤ 3 * (B - 1))
    (hk : E k ≠ 0) {x : ℤ}
    (hx : x ≡ ∑ i ∈ range (k + 1), E i * B ^ i [ZMOD B ^ (k + 1)]) :
    B ^ k / 2 < |x| := by
  have hfull := partial_sum_bound B hB E (k + 1) hE
  have hlead := distinguished_digit_bound B hB E k
    (fun i hi => hE i (Nat.lt_succ_of_lt hi)) hk
  have hp : 0 < B ^ k := pow_pos (by omega) k
  have hh : 0 < B ^ (k + 1) := pow_pos (by omega) (k + 1)
  have hdiv : 2 * (B ^ k / 2) ≤ B ^ k := by omega
  have hsmall : 2 * (B ^ k / 2) < B ^ (k + 1) := by
    rw [pow_succ]
    nlinarith
  apply no_small_representative hh hsmall _ _ hx
  · nlinarith
  · nlinarith

theorem small_residue_forces_zero (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k + 1, 50 * |E i| ≤ 3 * (B - 1))
    {x : ℤ} (hx : x ≡ ∑ i ∈ range (k + 1), E i * B ^ i [ZMOD B ^ (k + 1)])
    (hxsmall : |x| ≤ B ^ k / 2) : E k = 0 := by
  by_contra hk
  exact (not_lt_of_ge hxsmall) (digit_obstruction B hB E k hE hk hx)

theorem sum_modEq_prefix (B : ℤ) (E : ℕ → ℤ) (k m : ℕ) (hkm : k ≤ m) :
    (∑ i ∈ range m, E i * B ^ i) ≡
      (∑ i ∈ range k, E i * B ^ i) [ZMOD B ^ k] := by
  induction m, hkm using Nat.le_induction with
  | base => exact Int.ModEq.refl _
  | succ m hkm ih =>
    rw [sum_range_succ]
    have hdvd : B ^ k ∣ E m * B ^ m :=
      dvd_mul_of_dvd_right (pow_dvd_pow B hkm) _
    simpa using ih.add hdvd.modEq_zero_int

theorem polynomial_eval_modEq_prefix (p : Polynomial ℤ) (B : ℤ) (k : ℕ) :
    p.eval B ≡ (∑ i ∈ range k, p.coeff i * B ^ i) [ZMOD B ^ k] := by
  rw [Polynomial.eval_eq_sum_range' (n := max (p.natDegree + 1) k)
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))]
  exact sum_modEq_prefix B p.coeff k _ (le_max_right _ _)

theorem polynomial_obstruction (p : Polynomial ℤ) (B : ℤ) (hB : 2 ≤ B)
    (k : ℕ) (hE : ∀ i ≤ k, 50 * |p.coeff i| ≤ 3 * (B - 1))
    (hk : p.coeff k ≠ 0) {x : ℤ}
    (hx : x ≡ p.eval B [ZMOD B ^ (k + 1)]) : B ^ k / 2 < |x| := by
  exact digit_obstruction B hB p.coeff k
    (fun i hi => hE i (Nat.lt_succ_iff.mp hi)) hk
    (hx.trans (polynomial_eval_modEq_prefix p B (k + 1)))

theorem coefficient_bound_normalized {B L k e : ℤ}
    (hbase : 100 * k ^ 2 * L ^ 3 < B)
    (he : |e| ≤ 6 * k ^ 2 * L ^ 3) :
    50 * |e| ≤ 3 * (B - 1) := by
  have hbase' : 100 * k ^ 2 * L ^ 3 ≤ B - 1 := by omega
  nlinarith

theorem determinant_modEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A C : Matrix ι ι ℤ} {h : ℤ}
    (hAC : ∀ i j, A i j ≡ C i j [ZMOD h]) :
    A.det ≡ C.det [ZMOD h] := by
  simp only [Matrix.det_apply']
  apply Int.ModEq.sum
  intro σ _
  apply (Int.ModEq.refl _).mul
  exact Int.ModEq.prod (fun i _ => hAC (σ i) i)

theorem determinant_obstruction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι (Polynomial ℤ)) (B : ℤ) (hB : 2 ≤ B) (k : ℕ)
    (hcoeff : ∀ i ≤ k, 50 * |C.det.coeff i| ≤ 3 * (B - 1))
    (hk : C.det.coeff k ≠ 0) (A : Matrix ι ι ℤ)
    (hAC : ∀ i j, A i j ≡ (C i j).eval B [ZMOD B ^ (k + 1)]) :
    B ^ k / 2 < |A.det| := by
  apply polynomial_obstruction C.det B hB k hcoeff hk
  have heval := (Polynomial.evalRingHom B).map_det C
  change C.det.eval B = (C.map (Polynomial.eval B)).det at heval
  rw [heval]
  exact determinant_modEq hAC

theorem determinant_modEq_of_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℕ) (G : Matrix.SpecialLinearGroup ι (ZMod h))
    (A C : Matrix ι ι ℤ)
    (hAC : A.map (Int.castRingHom (ZMod h)) =
      (G : Matrix ι ι (ZMod h)) * C.map (Int.castRingHom (ZMod h))) :
    A.det ≡ C.det [ZMOD h] := by
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_det, Int.cast_det]
  change (A.map (Int.castRingHom (ZMod h))).det =
    (C.map (Int.castRingHom (ZMod h))).det
  rw [hAC, Matrix.det_mul, G.det_coe, one_mul]

end Problem355.DigitEncoding

end OAI
