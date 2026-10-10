import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeEvenBlockPartition
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimePlusStartingDigits

namespace OAI


namespace InternalCatalan

theorem boundaryFactor_even_multiple_reciprocal_reduction {p m : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm0 : 0 < m)
    (hmEven : m % 2 = 0) (hm : m < p) :
    (((p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p))).den : ZMod p) ≠ 0 ∧
      (((1 : ℚ) / ((m : ℚ) * boundaryFactor m)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p))).num : ZMod p) /
          (((p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p))).den : ZMod p) =
            (((1 : ℚ) / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
              (((1 : ℚ) / ((m : ℚ) * boundaryFactor m)).den : ZMod p) := by
  have hmpEven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hmpMod : (m * p) % p = 0 := Nat.mul_mod_left m p
  have hmpDiv : (m * p) / p = m := Nat.mul_div_cancel m hp.out.pos
  have hmpSmall : m * p < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hm hp.out.pos
  have hmSmall : m < p ^ 2 := by
    have hpp : p ≤ p * p := by
      have hp1 : 1 ≤ p := by have := hp.out.pos; omega
      simpa only [one_mul] using Nat.mul_le_mul_right p hp1
    simpa only [pow_two] using hm.trans_le hpp
  have hred := boundaryFactor_even_digit_reduction hp2 hmpEven
    (show ((m * p) % p) % 2 = 0 by rw [hmpMod])
  have hHres : ((boundaryFactor (m * p)).num : ZMod p) /
      ((boundaryFactor (m * p)).den : ZMod p) =
        ((boundaryFactor m).num : ZMod p) / ((boundaryFactor m).den : ZMod p) := by
    simpa [hmpDiv, hmpMod] using hred.2.2.2
  have hHv : padicValRat p (boundaryFactor (m * p)) = 0 :=
    boundaryFactor_even_odd_prime_eq_zero hp.out hp2 hmpEven hmpSmall
      (by rw [hmpMod])
  have hmv : padicValRat p (boundaryFactor m) = 0 :=
    boundaryFactor_even_odd_prime_eq_zero hp.out hp2 hmEven hmSmall
      (by simpa only [Nat.mod_eq_of_lt hm] using hmEven)
  have hmNatv : padicValRat p (m : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hm0 hm)]
    norm_num
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have h1v : padicValRat p ((m : ℚ) * boundaryFactor (m * p)) = 0 := by
    rw [padicValRat.mul hmq (boundaryFactor_ne_zero _), hmNatv, hHv]
    norm_num
  have h2v : padicValRat p ((m : ℚ) * boundaryFactor m) = 0 := by
    rw [padicValRat.mul hmq (boundaryFactor_ne_zero _), hmNatv, hmv]
    norm_num
  have h1 := rational_residue_mul (p := p) (a := (m : ℚ)) (b := boundaryFactor (m * p))
    (by simp) hred.1
  have h2 := rational_residue_mul (p := p) (a := (m : ℚ)) (b := boundaryFactor m)
    (by simp) (by simpa only [hmpDiv] using hred.2.1)
  have hi1 := rational_residue_inv
    (mul_ne_zero hmq (boundaryFactor_ne_zero (m * p))) h1v
  have hi2 := rational_residue_inv
    (mul_ne_zero hmq (boundaryFactor_ne_zero m)) h2v
  have hcancel : (p : ℚ) / (((m * p : ℕ) : ℚ) * boundaryFactor (m * p)) =
      ((m : ℚ) * boundaryFactor (m * p))⁻¹ := by
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [Nat.cast_mul]
    field_simp [hpq, hmq, boundaryFactor_ne_zero]
  simp only [hcancel, one_div]
  refine ⟨hi1.1, hi2.1, ?_⟩
  rw [hi1.2, hi2.2, h1.2, h2.2, hHres]





theorem boundaryFactor_even_reciprocal_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzEven : z % 2 = 0)
    (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) / ((z : ℚ) * boundaryFactor z)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz0
  rw [padicValRat.div hpq (mul_ne_zero hzq (boundaryFactor_ne_zero z)),
    padicValRat.self hp.one_lt,
    boundaryFactor_even_mul_odd_prime_valuation hp hp2 hzEven hz0 hz]
  split_ifs <;> norm_num

theorem boundaryFactor_even_reciprocal_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzEven : z % 2 = 0) (hz0 : z ≠ 0) (hz : z < p ^ 2) :
    (((p : ℚ) / ((z : ℚ) * boundaryFactor z)).den : ZMod p) ≠ 0 :=
  rational_den_ne_zero_of_valuation_nonneg
    (boundaryFactor_even_reciprocal_valuation_nonneg hp.out hp2 hzEven hz0 hz)

private theorem boundaryFactor_reciprocal_down_step (p z : ℕ) (hz : 0 < z) :
    (z : ℚ) * ((p : ℚ) / ((z : ℚ) * boundaryFactor z)) =
      ((z + 1 : ℕ) : ℚ) *
        ((p : ℚ) / (((z + 2 : ℕ) : ℚ) * boundaryFactor (z + 2))) := by
  rw [boundaryFactor_step]
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  have hz1q : ((z + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hzq, hz1q, boundaryFactor_ne_zero z]

private theorem evenBlock_cast_sub (p m n : ℕ) (hn : n ≤ m * p) :
    ((m * p - n : ℕ) : ZMod p) = -(n : ZMod p) := by
  rw [Nat.cast_sub hn]
  push_cast
  simp

theorem boundaryFactor_even_block_reciprocal_reduction {p m j : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0)
    (hm : m < p) (hj : 2 * j < p) :
    (((p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) *
      boundaryFactor (m * p - 2 * j))).den : ZMod p) ≠ 0 ∧
      ((centralCoeff j).den : ZMod p) ≠ 0 ∧
        ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p) ≠ 0 ∧
          (((p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) *
            boundaryFactor (m * p - 2 * j))).num : ZMod p) /
              (((p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) *
                boundaryFactor (m * p - 2 * j))).den : ZMod p) =
                  (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p)) *
                    (((1 / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
                      ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p)) := by
  have hbase := boundaryFactor_even_multiple_reciprocal_reduction hp2 hm0 hmEven hm
  have hmp : p ≤ m * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  have hmpsmall : m * p < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hm hp.out.pos
  have hmpeven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hzpos : ∀ u : ℕ, 2 * u < p → 0 < m * p - 2 * u := by
    intro u hu
    omega
  have hden : ∀ u : ℕ, 2 * u < p →
      (((p : ℚ) / (((m * p - 2 * u : ℕ) : ℚ) *
        boundaryFactor (m * p - 2 * u))).den : ZMod p) ≠ 0 := by
    intro u hu
    have heven : (m * p - 2 * u) % 2 = 0 := by omega
    exact boundaryFactor_even_reciprocal_den_ne_zero hp2 heven
      (Nat.ne_of_gt (hzpos u hu)) (by omega)
  have hcden : ∀ u : ℕ, ((centralCoeff u).den : ZMod p) ≠ 0 :=
    fun u => (centralCoeff_reduced_residue hp2 u).1
  refine ⟨hden j hj, hcden j, hbase.2.1, ?_⟩
  revert hj
  induction j with
  | zero =>
    intro hj
    simpa [centralCoeff] using hbase.2.2
  | succ j ih =>
    intro hj
    have hjprev : 2 * j < p := by omega
    have hz : 0 < m * p - 2 * (j + 1) := hzpos (j + 1) hj
    have hstep := boundaryFactor_reciprocal_down_step p
      (m * p - 2 * (j + 1)) hz
    have hback : m * p - 2 * (j + 1) + 2 = m * p - 2 * j := by omega
    rw [hback] at hstep
    have hs := rational_residue_nat_mul_eq (m * p - 2 * (j + 1))
      (m * p - 2 * (j + 1) + 1) (hden (j + 1) hj) (hden j hjprev) hstep
    have hc := rational_residue_nat_mul_eq (2 * j + 2) (2 * j + 1)
      (hcden (j + 1)) (hcden j) (centralCoeff_step j)
    have hmid : m * p - 2 * (j + 1) + 1 = m * p - (2 * j + 1) := by omega
    have hleftCast : ((m * p - 2 * (j + 1) : ℕ) : ZMod p) =
        -((2 * j + 2 : ℕ) : ZMod p) := by
      simpa only [show 2 * (j + 1) = 2 * j + 2 by omega] using
        evenBlock_cast_sub p m (2 * (j + 1)) (by omega)
    have hrightCast : ((m * p - 2 * (j + 1) + 1 : ℕ) : ZMod p) =
        -((2 * j + 1 : ℕ) : ZMod p) := by
      rw [hmid]
      exact evenBlock_cast_sub p m (2 * j + 1) (by omega)
    rw [hleftCast, hrightCast] at hs
    simp only [neg_mul, neg_inj] at hs
    have hnz : ((2 * j + 2 : ℕ) : ZMod p) ≠ 0 := by
      intro hzero
      have hd := (ZMod.natCast_eq_zero_iff (2 * j + 2) p).mp hzero
      have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 2) hd
      omega
    apply mul_left_cancel₀ hnz
    rw [hs, ih hjprev]
    calc
      _ = (((2 * j + 1 : ℕ) : ZMod p) *
          (((centralCoeff j).num : ZMod p) / ((centralCoeff j).den : ZMod p))) *
            (((1 / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
              ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p)) := by ring
      _ = (((2 * j + 2 : ℕ) : ZMod p) *
          (((centralCoeff (j + 1)).num : ZMod p) /
            ((centralCoeff (j + 1)).den : ZMod p))) *
              (((1 / ((m : ℚ) * boundaryFactor m)).num : ZMod p) /
                ((1 / ((m : ℚ) * boundaryFactor m)).den : ZMod p)) := by rw [hc]
      _ = _ := by ring

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

theorem boundaryMinusWeight_even_scaled_eq {p z : ℕ} (hzEven : z % 2 = 0) :
    (p : ℚ) ^ 2 * boundaryMinusWeight z =
      2 * ((p : ℚ) / ((z : ℚ) * boundaryFactor z)) ^ 2 := by
  rw [boundaryMinusWeight, ite_eq_left hzEven, div_pow, mul_pow]
  ring

theorem boundaryMinusWeight_even_block_sum_reduction {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0) (hm : m < p) :
    ((∑ j ∈ Finset.range ((p - 1) / 2 + 1),
      (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p) ≠ 0 ∧
      ((boundaryMinusWeight m).den : ZMod p) ≠ 0 ∧
        ((∑ j ∈ Finset.range ((p - 1) / 2 + 1),
          (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).num : ZMod p) /
            ((∑ j ∈ Finset.range ((p - 1) / 2 + 1),
              (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p) =
                (-1 : ZMod p) ^ ((p - 1) / 2) *
                  (((boundaryMinusWeight m).num : ZMod p) /
                    ((boundaryMinusWeight m).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let I : ℚ := 1 / ((m : ℚ) * boundaryFactor m)
  let F : ℕ → ℚ := fun j =>
    (p : ℚ) / (((m * p - 2 * j : ℕ) : ℚ) * boundaryFactor (m * p - 2 * j))
  have htwo : R 2 = 2 := by norm_num [R]
  have hsquare {q : ℚ} (hd : (q.den : ZMod p) ≠ 0) :
      ((q ^ 2).den : ZMod p) ≠ 0 ∧ R (q ^ 2) = R q ^ 2 := by
    simpa only [R, pow_two] using rational_residue_mul (p := p) hd hd
  have hI : (I.den : ZMod p) ≠ 0 :=
    (boundaryFactor_even_multiple_reciprocal_reduction hp2 hm0 hmEven hm).2.1
  have hIsq := hsquare hI
  have hmweight : boundaryMinusWeight m = 2 * I ^ 2 := by
    dsimp only [I]
    simpa using (boundaryMinusWeight_even_scaled_eq (p := 1) hmEven)
  have hmw := rational_residue_mul (p := p) (a := (2 : ℚ)) (b := I ^ 2) (by norm_num) hIsq.1
  have hmwden : ((boundaryMinusWeight m).den : ZMod p) ≠ 0 := by
    simpa only [hmweight] using hmw.1
  have hmwR : R (boundaryMinusWeight m) = 2 * R I ^ 2 := by
    rw [hmweight]
    calc
      _ = R 2 * R (I ^ 2) := hmw.2
      _ = _ := by rw [htwo, hIsq.2]
  have hmp : p ≤ m * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  have hmpeven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hterm (j : ℕ) (hj : j ∈ Finset.range ((p - 1) / 2 + 1)) :
      (((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p) ≠ 0 ∧
        R ((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)) =
          R (centralCoeff j) ^ 2 * R (boundaryMinusWeight m) := by
    have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
    have hjlt : 2 * j < p := by
      have := Finset.mem_range.mp hj
      omega
    have hzEven : (m * p - 2 * j) % 2 = 0 := by omega
    have hblock := boundaryFactor_even_block_reciprocal_reduction hp2 hm0 hmEven hm hjlt
    have hF : R (F j) = R (centralCoeff j) * R I := hblock.2.2.2
    have hFsq := hsquare hblock.1
    have hFsqR : R (F j ^ 2) = R (F j) ^ 2 := hFsq.2
    have hprod := rational_residue_mul (p := p) (a := (2 : ℚ)) (b := F j ^ 2)
      (by norm_num) hFsq.1
    have heq : (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j) = 2 * F j ^ 2 :=
      boundaryMinusWeight_even_scaled_eq hzEven
    refine ⟨by simpa only [heq] using hprod.1, ?_⟩
    rw [heq]
    calc
      _ = R 2 * R (F j ^ 2) := hprod.2
      _ = R (centralCoeff j) ^ 2 * R (boundaryMinusWeight m) := by
        rw [htwo, hFsqR, hF, hmwR]
        ring
  have hsum := rational_residue_sum (p := p) (Finset.range ((p - 1) / 2 + 1))
    (fun j => (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j))
    (fun j hj => (hterm j hj).1)
  refine ⟨hsum.1, hmwden, ?_⟩
  rw [hsum.2]
  calc
    _ = ∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        R (centralCoeff j) ^ 2 * R (boundaryMinusWeight m) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).2
    _ = (∑ j ∈ Finset.range ((p - 1) / 2 + 1), R (centralCoeff j) ^ 2) *
        R (boundaryMinusWeight m) := (Finset.sum_mul _ _ _).symm
    _ = _ := by
      have hc : (∑ j ∈ Finset.range ((p - 1) / 2 + 1), R (centralCoeff j) ^ 2) =
          (-1 : ZMod p) ^ ((p - 1) / 2) := centralCoeff_residue_square_block hp2
      rw [hc]

end InternalCatalan

end


namespace InternalCatalan

private theorem lowerStrip_pred_succ (n : ℕ) :
    momentScalarPred (n + 1) = momentScalar n := by
  simp [momentScalarPred]

theorem momentLowerStrip_term_zero {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : u + j + 1 < p ^ 2) (hnd : ¬p ∣ j + 1) :
    (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
        (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) = 0 := by
  have hs := momentScalarPred_prime_digit_reduction hp2 hb
  have hj : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hnd ((ZMod.natCast_eq_zero_iff (j + 1) p).mp hzero)
  have hf := nat_fraction_reduced_residue p (j + 1) hj
  have hm := rational_residue_mul hs.1 hf.1
  have heq : (p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (u + j + 1)) *
        ((p : ℚ) / ((j + 1 : ℕ) : ℚ)) := by
    rw [lowerStrip_pred_succ]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hm.1
  · rw [heq, hm.2, hf.2]
    simp

theorem momentLowerStrip_term_multiple {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : u + j + 1 < p ^ 2) (hd : p ∣ j + 1) :
    (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      ((momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
          (((p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ)).num : ZMod p) /
                ((momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ)).den : ZMod p)) := by
  have hsucc : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hd
  have hjmul : j + 1 = p * (j / p + 1) := by
    rw [← hsucc]
    exact (Nat.mul_div_cancel' hd).symm
  have hquot : (u + j + 1) / p = u / p + (j / p + 1) := by
    rw [show u + j + 1 = u + (j + 1) by omega, hjmul]
    exact Nat.add_mul_div_left u (j / p + 1) hp.out.pos
  have hrem : (u + j + 1) % p = u % p := by
    rw [show u + j + 1 = u + (j + 1) by omega, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hd, add_zero, Nat.mod_mod]
  have hzsmall : (u + j + 1) / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hb)
  have hqsmall : j / p + 1 < p := by
    rw [hquot] at hzsmall
    exact (Nat.le_add_left (j / p + 1) (u / p)).trans_lt hzsmall
  have hqnot : ¬p ∣ j / p + 1 :=
    Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (j / p)) hqsmall
  have hqden : ((j / p + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hqnot ((ZMod.natCast_eq_zero_iff (j / p + 1) p).mp hzero)
  have hf := nat_fraction_reduced_residue 1 (j / p + 1) hqden
  simp only [Nat.cast_one] at hf
  have hs := momentScalarPred_prime_digit_reduction hp2 hb
  have hl := rational_residue_mul hs.1 hf.1
  have hr := rational_residue_mul hs.2.1 hf.1
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hqq : ((j / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hjcast : ((j + 1 : ℕ) : ℚ) =
      (p : ℚ) * ((j / p + 1 : ℕ) : ℚ) := by exact_mod_cast hjmul
  have hpred : momentScalarPred ((u + j + 1) / p) = momentScalar (u / p + j / p) := by
    rw [hquot, show u / p + (j / p + 1) = (u / p + j / p) + 1 by omega,
      lowerStrip_pred_succ]
  have hleft : (p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred (u + j + 1)) *
        (1 / ((j / p + 1 : ℕ) : ℚ)) := by
    rw [lowerStrip_pred_succ, hjcast]
    field_simp [hpq, hqq]
  have hright : momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ) =
      momentScalarPred ((u + j + 1) / p) * (1 / ((j / p + 1 : ℕ) : ℚ)) := by
    rw [hpred]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl.1
  · rw [hright]
    exact hr.1
  · rw [hleft, hl.2, hs.2.2, hrem, hright, hr.2]
    ring

end InternalCatalan


section

open scoped BigOperators

namespace InternalCatalan

private theorem parityBoundarySum_even_range (f : ℕ → ℚ) (a : ℕ) :
    parityBoundarySum f (2 * a) =
      ∑ k ∈ Finset.range a, f (2 * (k + 1)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 2 by omega,
      parityBoundarySum_step, ih, Finset.sum_range_succ]
    congr 2

private theorem boundaryMinusWeight_even_residue_block {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0) (hm : m < p) :
    (∑ j ∈ Finset.range ((p - 1) / 2 + 1),
      (((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)).den : ZMod p)) =
      (-1 : ZMod p) ^ ((p - 1) / 2) *
        (((boundaryMinusWeight m).num : ZMod p) / ((boundaryMinusWeight m).den : ZMod p)) := by
  have hmp : p ≤ m * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ m by omega)
  have hmpsmall : m * p < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hm hp.out.pos
  have hmpeven : (m * p) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hsum := rational_residue_sum (p := p) (Finset.range ((p - 1) / 2 + 1))
    (fun j => (p : ℚ) ^ 2 * boundaryMinusWeight (m * p - 2 * j)) (by
      intro j hj
      have hjlt : 2 * j < p := by have := Finset.mem_range.mp hj; omega
      exact boundaryMinusWeight_even_scaled_den_ne_zero hp2 (by omega)
        (by omega) (by omega))
  exact hsum.2.symm.trans
    (boundaryMinusWeight_even_block_sum_reduction hp2 hm0 hmEven hm).2.2

private theorem boundaryMinus_small_even_residue_sum {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p) :
    ((boundaryMinus u).num : ZMod p) / ((boundaryMinus u).den : ZMod p) =
      (((boundaryFactor u).num : ZMod p) / ((boundaryFactor u).den : ZMod p)) *
        ∑ a ∈ Finset.range (u / 2),
          ((boundaryMinusWeight (2 * (a + 1))).num : ZMod p) /
            ((boundaryMinusWeight (2 * (a + 1))).den : ZMod p) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hsum := rational_residue_sum (p := p) (Finset.range (u / 2))
    (fun a => boundaryMinusWeight (2 * (a + 1))) (by
      intro a ha
      have ha' := Finset.mem_range.mp ha
      exact (boundaryMinusWeight_even_block_sum_reduction hp2
        (by omega : 0 < 2 * (a + 1)) (by omega) (by omega)).2.1)
  have hH : ((boundaryFactor u).den : ZMod p) ≠ 0 :=
    (boundaryFactor_even_digit_reduction hp2 huEven
      (by simpa only [Nat.mod_eq_of_lt hu] using huEven)).1
  have hprod := rational_residue_mul (p := p) hH hsum.1
  have hparity : parityBoundarySum boundaryMinusWeight u =
      ∑ a ∈ Finset.range (u / 2), boundaryMinusWeight (2 * (a + 1)) := by
    have h := parityBoundarySum_even_range boundaryMinusWeight (u / 2)
    simpa only [show 2 * (u / 2) = u by omega] using h
  rw [boundaryMinus_explicit, hparity]
  calc
    _ = R (boundaryFactor u) *
        R (∑ a ∈ Finset.range (u / 2), boundaryMinusWeight (2 * (a + 1))) := hprod.2
    _ = _ := by
      congr 1
      exact hsum.2

theorem boundaryMinus_even_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huEven : u % 2 = 0) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((boundaryMinus (u / p)).num : ZMod p) /
                ((boundaryMinus (u / p)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hP : u / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hu)
  have hr : u % p < p := Nat.mod_lt _ hp.out.pos
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have htarget : ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ hP)
  refine ⟨boundaryMinus_prime_sq_scaled_den_ne_zero hp2 hu, htarget, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryMinus u) =
    (oddPrimeWeight p).coeff (p - 1 - u % p) * R (boundaryMinus (u / p))
  by_cases hrEven : (u % p) % 2 = 0
  · have hPpar := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div u p)
    simp only [Nat.add_mod, Nat.mul_mod, hrEven, hpOdd, zero_add, one_mul,
      Nat.mod_mod, huEven] at hPpar
    have hsupport :
        (∑ z ∈ Finset.range (u + 1),
          if 0 < z ∧ z % 2 = 0 then R ((p : ℚ) ^ 2 * boundaryMinusWeight z) else 0) =
        ∑ z ∈ (Finset.range (u + 1)).filter
          (fun z => 0 < z ∧ z % 2 = 0 ∧ (z % p = 0 ∨ (z % p) % 2 = 1)),
            R ((p : ℚ) ^ 2 * boundaryMinusWeight z) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hz0 : 0 < z
      · by_cases hzEven : z % 2 = 0
        · by_cases hsurvive : z % p = 0 ∨ (z % p) % 2 = 1
          · simp [hz0, hzEven, hsurvive]
          · have hzero := boundaryMinusWeight_even_no_carry_reduction hp2 hz0 hzEven
              (by have := Finset.mem_range.mp hz; omega)
              (fun h => hsurvive (Or.inl h)) (by omega)
            have hzR : R ((p : ℚ) ^ 2 * boundaryMinusWeight z) = 0 := hzero.2
            simp [hz0, hzEven, hsurvive, hzR]
        · simp [hzEven]
      · simp [hz0]
    have hS :
        (∑ z ∈ Finset.range (u + 1),
          if 0 < z ∧ z % 2 = 0 then R ((p : ℚ) ^ 2 * boundaryMinusWeight z) else 0) =
          (-1 : ZMod p) ^ ((p - 1) / 2) *
            ∑ a ∈ Finset.range ((u / p) / 2), R (boundaryMinusWeight (2 * (a + 1))) := by
      rw [hsupport, even_surviving_sum_eq_complete_blocks hpOdd huEven hrEven]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      exact boundaryMinusWeight_even_residue_block hp2 (by omega)
        (by omega) (by omega)
    have hH := boundaryFactor_even_digit_reduction hp2 huEven hrEven
    have hHR : R (boundaryFactor u) =
        R (boundaryFactor (u / p)) * R (centralCoeff ((u % p) / 2)) := hH.2.2.2
    have hc : R (centralCoeff ((u % p) / 2)) = (oddPrimeWeight p).coeff (u % p) := by
      change ((centralCoeff ((u % p) / 2)).num : ZMod p) /
        ((centralCoeff ((u % p) / 2)).den : ZMod p) = _
      rw [(centralCoeff_reduced_residue hp2 ((u % p) / 2)).2]
      symm
      simpa only [show 2 * ((u % p) / 2) = u % p by omega] using
        (oddPrimeWeight_coeff_central hp2 (show 2 * ((u % p) / 2) < p by omega))
    have hB := boundaryMinus_small_even_residue_sum hp2 hPpar hP
    have hBR : R (boundaryMinus (u / p)) =
        R (boundaryFactor (u / p)) *
          ∑ a ∈ Finset.range ((u / p) / 2), R (boundaryMinusWeight (2 * (a + 1))) := hB
    have hbigR : R ((p : ℚ) ^ 2 * boundaryMinus u) =
        R (boundaryFactor u) *
          ∑ z ∈ Finset.range (u + 1),
            if 0 < z ∧ z % 2 = 0 then R ((p : ℚ) ^ 2 * boundaryMinusWeight z) else 0 :=
      (boundaryMinus_even_scaled_residue_sum hp2 huEven hu).2
    rw [hbigR, hS, hHR, oddPrimeWeight_coeff_reverse hp.out hp2 hr, ← hc, hBR]
    ring
  · have hzero := boundaryMinus_even_odd_remainder_zero hp2 huEven hu (by omega)
    have hzeroR : R ((p : ℚ) ^ 2 * boundaryMinus u) = 0 := hzero.2
    have hcoeff : (oddPrimeWeight p).coeff (p - 1 - u % p) = 0 := by
      rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
        oddPrimeWeight_coeff_odd p (u % p) hrEven, mul_zero]
    rw [hzeroR, hcoeff, zero_mul]

end InternalCatalan

end


namespace InternalCatalan

open scoped BigOperators

def momentLowerStrip (u j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range j, momentScalar (u + k) / ((k + 1 : ℕ) : ℚ)

@[simp] theorem momentLowerStrip_zero (u : ℕ) : momentLowerStrip u 0 = 0 := by
  simp [momentLowerStrip]

theorem momentLowerStrip_succ (u j : ℕ) :
    momentLowerStrip u (j + 1) = momentLowerStrip u j +
      momentScalar (u + j) / ((j + 1 : ℕ) : ℚ) := by
  unfold momentLowerStrip
  rw [Finset.sum_range_succ]

theorem momentRat_lower_strip (u j : ℕ) :
    momentRat (u + j) j = boundaryMinus u - momentLowerStrip u j := by
  simpa only [momentLowerStrip, Nat.add_sub_cancel_right] using
    (momentRat_of_le (by omega : j ≤ u + j))

theorem momentLowerStrip_prime_digit_reduction {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : u + j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentLowerStrip u j).den : ZMod p) ≠ 0 ∧
      ((momentLowerStrip (u / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentLowerStrip u j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentLowerStrip u j).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((momentLowerStrip (u / p) (j / p)).num : ZMod p) /
                ((momentLowerStrip (u / p) (j / p)).den : ZMod p)) := by
  revert hbound
  induction j with
  | zero => intro hbound; simp
  | succ j ih =>
    intro hbound
    have hprev := ih (by omega : u + j < p ^ 2)
    have hscale : (p : ℚ) ^ 2 * momentLowerStrip u (j + 1) =
        (p : ℚ) ^ 2 * momentLowerStrip u j +
          (p : ℚ) ^ 2 * (momentScalar (u + j) / ((j + 1 : ℕ) : ℚ)) := by
      rw [momentLowerStrip_succ, mul_add]
    by_cases hdiv : p ∣ j + 1
    · have ht := momentLowerStrip_term_multiple hp2
        (by omega : u + j + 1 < p ^ 2) hdiv
      have hquot : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hdiv
      have hsmall : momentLowerStrip (u / p) ((j + 1) / p) =
          momentLowerStrip (u / p) (j / p) +
            momentScalar (u / p + j / p) / ((j / p + 1 : ℕ) : ℚ) := by
        rw [hquot, momentLowerStrip_succ]
      have hl := rational_residue_add hprev.1 ht.1
      have hr := rational_residue_add hprev.2.1 ht.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hsmall]
        exact hr.1
      · rw [hscale, hl.2, hprev.2.2, ht.2.2, hsmall, hr.2]
        ring
    · have ht := momentLowerStrip_term_zero hp2
        (by omega : u + j + 1 < p ^ 2) hdiv
      have hquot : (j + 1) / p = j / p := Nat.succ_div_of_not_dvd hdiv
      have hl := rational_residue_add hprev.1 ht.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, ht.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan



namespace InternalCatalan

theorem boundaryMinus_prime_digit_reduction {p u : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryMinus u).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((boundaryMinus (u / p)).num : ZMod p) /
                ((boundaryMinus (u / p)).den : ZMod p)) := by
  by_cases hEven : u % 2 = 0
  · exact boundaryMinus_even_digit_reduction hp2 hEven hu
  · exact boundaryMinus_odd_digit_reduction hp2 (by omega) hu

theorem momentRat_lower_prime_digit_reduction {p u j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : u + j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat (u + j) j).den : ZMod p) ≠ 0 ∧
      ((momentRat (u / p + j / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat (u + j) j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat (u + j) j).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - u % p) *
              (((momentRat (u / p + j / p) (j / p)).num : ZMod p) /
                ((momentRat (u / p + j / p) (j / p)).den : ZMod p)) := by
  have hstart := boundaryMinus_prime_digit_reduction hp2 (show u < p ^ 2 by omega)
  have hstrip := momentLowerStrip_prime_digit_reduction hp2 hbound
  have hl := rational_residue_sub hstart.1 hstrip.1
  have hr := rational_residue_sub hstart.2.1 hstrip.2.1
  have hleft : (p : ℚ) ^ 2 * momentRat (u + j) j =
      (p : ℚ) ^ 2 * boundaryMinus u - (p : ℚ) ^ 2 * momentLowerStrip u j := by
    rw [momentRat_lower_strip, mul_sub]
  have hright : momentRat (u / p + j / p) (j / p) =
      boundaryMinus (u / p) - momentLowerStrip (u / p) (j / p) :=
    momentRat_lower_strip (u / p) (j / p)
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl.1
  · rw [hright]
    exact hr.1
  · rw [hleft, hl.2, hstart.2.2, hstrip.2.2, hright, hr.2]
    ring

theorem momentRat_prime_digit_reduction_of_le {p i j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hji : j ≤ i) (hi : i < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      ((momentRat ((i - j) / p + j / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - (i - j) % p) *
              (((momentRat ((i - j) / p + j / p) (j / p)).num : ZMod p) /
                ((momentRat ((i - j) / p + j / p) (j / p)).den : ZMod p)) := by
  simpa only [Nat.sub_add_cancel hji] using
    momentRat_lower_prime_digit_reduction hp2
      (show i - j + j < p ^ 2 by omega)

end InternalCatalan

end OAI
