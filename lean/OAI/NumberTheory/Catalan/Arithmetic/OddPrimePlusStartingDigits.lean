import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeEvenStartingZero

namespace OAI


namespace InternalCatalan

theorem centralCoeff_half_prime_reduced_residue {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    ((centralCoeff ((p - 1) / 2)).den : ZMod p) ≠ 0 ∧
      ((centralCoeff ((p - 1) / 2)).num : ZMod p) /
        ((centralCoeff ((p - 1) / 2)).den : ZMod p) =
          (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hk : 2 * ((p - 1) / 2) < p := by omega
  have hc := centralCoeff_reduced_residue hp2 ((p - 1) / 2)
  refine ⟨hc.1, ?_⟩
  rw [hc.2]
  simpa using (oddPrimeWeight_centralCoeff_identity hp2 hk).symm

theorem boundaryFactor_odd_multiple_reduction {p P : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hPOdd : P % 2 = 1) (hP : P < p) :
    (((p : ℚ) * boundaryFactor (P * p)).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor P).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * boundaryFactor (P * p)).num : ZMod p) /
          (((p : ℚ) * boundaryFactor (P * p)).den : ZMod p) =
            (-1 : ZMod p) ^ ((p - 1) / 2) *
              (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by
  let A : ℕ := (P - 1) / 2
  let s : ℕ := (p - 1) / 2
  let l : ℕ := p * A + s
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hPpos : 0 < P := by omega
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hA : 2 * A + 1 = P := by dsimp [A]; omega
  have hs : 2 * s + 1 = p := by dsimp [s]; omega
  have hslt : s < p := by omega
  have hl : 2 * l + 1 = P * p := by dsimp [l]; nlinarith
  have hlmod : l % p = s := by
    dsimp only [l]
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hslt]
  have hldiv : l / p = A := by
    dsimp only [l]
    rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hslt, add_zero]
  have hncarry : 2 * (l % p) < p := by rw [hlmod]; omega
  have hcl := centralCoeff_digit_no_carry hp2 hncarry
  have hsign := centralCoeff_half_prime_reduced_residue (p := p) hp2
  have hsignR : R (centralCoeff s) = (-1 : ZMod p) ^ s := hsign.2
  have hsplit : R (centralCoeff l) = R (centralCoeff A) * (-1 : ZMod p) ^ s := by
    have hsplitR : R (centralCoeff l) = R (centralCoeff A) * R (centralCoeff s) := by
      simpa only [R, hldiv, hlmod] using hcl.2.2.2
    rw [hsignR] at hsplitR
    exact hsplitR
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hPpos)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hPval : padicValRat p (P : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hPpos hP)]
    norm_num
  have hcAval : padicValRat p (centralCoeff A) = 0 :=
    centralCoeff_odd_prime_valuation_zero_of_lt hp.out hp2 (by omega)
  have hclval : padicValRat p (centralCoeff l) = 0 := by
    have hbound : 2 * l < p ^ 2 := by nlinarith [hp.out.pos]
    rw [centralCoeff_odd_prime_single_carry hp.out hp2 hbound,
      ite_eq_right (by omega : ¬p ≤ 2 * (l % p))]
  have hprodAval : padicValRat p ((P : ℚ) * centralCoeff A) = 0 := by
    rw [padicValRat.mul hPq (centralCoeff_ne_zero A), hPval, hcAval, add_zero]
  have hprodlval : padicValRat p ((P : ℚ) * centralCoeff l) = 0 := by
    rw [padicValRat.mul hPq (centralCoeff_ne_zero l), hPval, hclval, add_zero]
  have hinvA := rational_residue_inv (mul_ne_zero hPq (centralCoeff_ne_zero A)) hprodAval
  have hinvl := rational_residue_inv (mul_ne_zero hPq (centralCoeff_ne_zero l)) hprodlval
  have hinvAR : R (((P : ℚ) * centralCoeff A)⁻¹) =
      (R ((P : ℚ) * centralCoeff A))⁻¹ := hinvA.2
  have hinvlR : R (((P : ℚ) * centralCoeff l)⁻¹) =
      (R ((P : ℚ) * centralCoeff l))⁻¹ := hinvl.2
  have hmulA := rational_residue_mul (a := (P : ℚ)) (b := centralCoeff A)
    (by simp) (centralCoeff_reduced_residue (p := p) hp2 A).1
  have hmull := rational_residue_mul (a := (P : ℚ)) (b := centralCoeff l)
    (by simp) (centralCoeff_reduced_residue (p := p) hp2 l).1
  have hRA : R ((P : ℚ) * centralCoeff A) = (P : ZMod p) * R (centralCoeff A) := by
    simpa [R] using hmulA.2
  have hRl : R ((P : ℚ) * centralCoeff l) = (P : ZMod p) * R (centralCoeff l) := by
    simpa [R] using hmull.2
  have hboundaryA : boundaryFactor P = ((P : ℚ) * centralCoeff A)⁻¹ := by
    have heq := boundaryFactor_odd A
    rw [hA, one_div] at heq
    exact heq
  have hboundaryl : (p : ℚ) * boundaryFactor (P * p) =
      ((P : ℚ) * centralCoeff l)⁻¹ := by
    have heq := boundaryFactor_odd l
    rw [hl] at heq
    rw [heq, Nat.cast_mul]
    field_simp [hPq, hpq, centralCoeff_ne_zero l]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hboundaryl] using hinvl.1
  · simpa only [hboundaryA] using hinvA.1
  · change R ((p : ℚ) * boundaryFactor (P * p)) = (-1 : ZMod p) ^ s * R (boundaryFactor P)
    rw [hboundaryl, hboundaryA]
    rw [hinvlR, hinvAR, hRl, hRA, hsplit]
    simp only [mul_inv_rev]
    ring_nf
    norm_num
    ring





theorem boundaryFactor_odd_even_digit_reduction {p P k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hPOdd : P % 2 = 1) (hP : P < p) (hk : 2 * k < p) :
    (((p : ℚ) * boundaryFactor (P * p + 2 * k)).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor P).den : ZMod p) ≠ 0 ∧
        ((centralCoeff k).den : ZMod p) ≠ 0 ∧
          (((p : ℚ) * boundaryFactor (P * p + 2 * k)).num : ZMod p) /
            (((p : ℚ) * boundaryFactor (P * p + 2 * k)).den : ZMod p) =
              (-1 : ZMod p) ^ ((p - 1) / 2) *
                (((centralCoeff k).num : ZMod p) / ((centralCoeff k).den : ZMod p)) *
                  (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hbase := boundaryFactor_odd_multiple_reduction hp2 hPOdd hP
  have hden : ∀ u : ℕ, 2 * u < p →
      (((p : ℚ) * boundaryFactor (P * p + 2 * u)).den : ZMod p) ≠ 0 := by
    intro u hu
    have hodd : (P * p + 2 * u) % 2 = 1 := by
      simp [Nat.add_mod, Nat.mul_mod, hPOdd, hpOdd]
    have hmul := Nat.mul_le_mul_right p (show P + 1 ≤ p by omega)
    have hsmall : P * p + 2 * u < p ^ 2 := by nlinarith
    exact (boundaryFactor_odd_integral_denominators hp2 hodd hsmall).2
  have hcden : ∀ u : ℕ, ((centralCoeff u).den : ZMod p) ≠ 0 :=
    fun u => (centralCoeff_reduced_residue hp2 u).1
  refine ⟨hden k hk, hbase.2.1, hcden k, ?_⟩
  revert hk
  induction k with
  | zero =>
    intro hk
    simpa using hbase.2.2
  | succ k ih =>
    intro hk
    have hkprev : 2 * k < p := by omega
    have hzstep :
        (((P * p + 2 * k + 2 : ℕ) : ℚ)) *
            ((p : ℚ) * boundaryFactor (P * p + 2 * (k + 1))) =
          (((P * p + 2 * k + 1 : ℕ) : ℚ)) *
            ((p : ℚ) * boundaryFactor (P * p + 2 * k)) := by
      rw [show P * p + 2 * (k + 1) = (P * p + 2 * k) + 2 by omega]
      calc
        _ = (p : ℚ) * ((((P * p + 2 * k + 2 : ℕ) : ℚ)) *
            boundaryFactor (P * p + 2 * k + 2)) := by ring
        _ = (p : ℚ) * ((((P * p + 2 * k + 1 : ℕ) : ℚ)) *
            boundaryFactor (P * p + 2 * k)) := by rw [boundaryFactor_step]
        _ = _ := by ring
    have hs := rational_residue_nat_mul_eq (P * p + 2 * k + 2) (P * p + 2 * k + 1)
      (hden (k + 1) hk) (hden k hkprev) hzstep
    have hc := rational_residue_nat_mul_eq (2 * k + 2) (2 * k + 1)
      (hcden (k + 1)) (hcden k) (centralCoeff_step k)
    have hcast (v : ℕ) : ((P * p + v : ℕ) : ZMod p) = (v : ZMod p) := by
      push_cast
      simp
    rw [show P * p + 2 * k + 2 = P * p + (2 * k + 2) by omega,
      show P * p + 2 * k + 1 = P * p + (2 * k + 1) by omega,
      hcast, hcast] at hs
    have hnz : ((2 * k + 2 : ℕ) : ZMod p) ≠ 0 := by
      intro hzero
      have hd := (ZMod.natCast_eq_zero_iff (2 * k + 2) p).mp hzero
      have hle := Nat.le_of_dvd (by omega : 0 < 2 * k + 2) hd
      omega
    apply mul_left_cancel₀ hnz
    rw [hs, ih hkprev]
    calc
      _ = (-1 : ZMod p) ^ ((p - 1) / 2) *
          (((2 * k + 1 : ℕ) : ZMod p) *
            (((centralCoeff k).num : ZMod p) / ((centralCoeff k).den : ZMod p))) *
              (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by ring
      _ = (-1 : ZMod p) ^ ((p - 1) / 2) *
          (((2 * k + 2 : ℕ) : ZMod p) *
            (((centralCoeff (k + 1)).num : ZMod p) / ((centralCoeff (k + 1)).den : ZMod p))) *
              (((boundaryFactor P).num : ZMod p) / ((boundaryFactor P).den : ZMod p)) := by rw [hc]
      _ = _ := by ring

theorem boundaryFactor_odd_even_remainder_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2)
    (hrEven : (z % p) % 2 = 0) :
    (((p : ℚ) * boundaryFactor z).den : ZMod p) ≠ 0 ∧
      ((boundaryFactor (z / p)).den : ZMod p) ≠ 0 ∧
        ((centralCoeff ((z % p) / 2)).den : ZMod p) ≠ 0 ∧
          (((p : ℚ) * boundaryFactor z).num : ZMod p) /
            (((p : ℚ) * boundaryFactor z).den : ZMod p) =
              (-1 : ZMod p) ^ ((p - 1) / 2) *
                (((centralCoeff ((z % p) / 2)).num : ZMod p) /
                  ((centralCoeff ((z % p) / 2)).den : ZMod p)) *
                    (((boundaryFactor (z / p)).num : ZMod p) /
                      ((boundaryFactor (z / p)).den : ZMod p)) := by
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hdecomp := Nat.mod_add_div z p
  have hpar := congrArg (fun n : ℕ => n % 2) hdecomp
  simp only [Nat.add_mod, Nat.mul_mod, hrEven, hpOdd, zero_add, one_mul,
    Nat.mod_mod, hzOdd] at hpar
  have hP : z / p < p := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hz)
  have hr : 2 * ((z % p) / 2) = z % p := by omega
  have heq : (z / p) * p + 2 * ((z % p) / 2) = z := by
    rw [hr, Nat.mul_comm]
    omega
  have hk : 2 * ((z % p) / 2) < p := by rw [hr]; exact Nat.mod_lt _ hp.out.pos
  simpa only [heq] using boundaryFactor_odd_even_digit_reduction hp2 hpar hP hk





private theorem boundaryFactor_small_valuation_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < p) : padicValRat p (boundaryFactor z) = 0 := by
  have hsq : z < p ^ 2 := by nlinarith [hp.out.one_lt]
  by_cases hEven : z % 2 = 0
  · rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 hEven hsq,
      Nat.mod_eq_of_lt hz]
    simp [hEven]
  · have hOdd : z % 2 = 1 := by omega
    rw [boundaryFactor_odd_prime_valuation hp.out hp2 hOdd hsq,
      Nat.mod_eq_of_lt hz]
    simp [hOdd]

theorem boundaryPlusWeight_small_den_ne_zero {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hz : z < p) :
    ((boundaryPlusWeight z).den : ZMod p) ≠ 0 := by
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hvz : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hz0 hz)]
    norm_num
  apply rational_den_ne_zero_of_valuation_nonneg
  rw [boundaryPlusWeight,
    padicValRat.div (by norm_num : (2 : ℚ) ≠ 0)
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)),
    padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
    padicValRat.pow, hvz, boundaryFactor_small_valuation_zero hp2 hz]
  simpa using zero_le_padicValRat_of_nat (p := p) 2

theorem boundaryPlusWeight_even_nonmultiple_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz0 : 0 < z) (hzEven : z % 2 = 0) (hz : z < p ^ 2)
    (hnon : ¬p ∣ z) :
    (((p : ℚ) ^ 2 * boundaryPlusWeight z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * boundaryPlusWeight z).num : ZMod p) /
        (((p : ℚ) ^ 2 * boundaryPlusWeight z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz0)
  have hw : boundaryPlusWeight z ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z))
  have hvz : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnon]
    norm_num
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  rw [padicValRat.mul (pow_ne_zero 2 hpq) hw, padicValRat.pow,
    padicValRat.self hp.out.one_lt, boundaryPlusWeight,
    padicValRat.div (by norm_num : (2 : ℚ) ≠ 0)
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)),
    padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
    padicValRat.pow, hvz,
    boundaryFactor_even_odd_prime_valuation hp.out hp2 hzEven hz]
  split_ifs <;> omega

theorem boundaryPlusWeight_odd_nonmultiple_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hzOdd : z % 2 = 1) (hz : z < p ^ 2) (hnon : ¬p ∣ z) :
    (((p : ℚ) * boundaryPlusWeight z).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) * boundaryPlusWeight z).num : ZMod p) /
        (((p : ℚ) * boundaryPlusWeight z).den : ZMod p) = 0 := by
  apply rational_residue_zero_of_positive_valuation
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  have hw : boundaryPlusWeight z ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z))
  have hvz : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnon]
    norm_num
  have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
  rw [padicValRat.mul hpq hw, padicValRat.self hp.out.one_lt, boundaryPlusWeight,
    padicValRat.div (by norm_num : (2 : ℚ) ≠ 0)
      (mul_ne_zero (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z)),
    padicValRat.mul (pow_ne_zero 2 hzq) (boundaryFactor_ne_zero z),
    padicValRat.pow, hvz, boundaryFactor_odd_prime_valuation hp.out hp2 hzOdd hz]
  split_ifs <;> omega

private theorem two_div_square_mul_residue {p m : ℕ} [hp : Fact p.Prime]
    (hm0 : 0 < m) (hm : m < p) {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat p q = 0) :
    ((2 / ((m : ℚ) ^ 2 * q)).den : ZMod p) ≠ 0 ∧
      ((2 / ((m : ℚ) ^ 2 * q)).num : ZMod p) /
        ((2 / ((m : ℚ) ^ 2 * q)).den : ZMod p) =
          (((2 / (m : ℚ) ^ 2).num : ZMod p) /
            ((2 / (m : ℚ) ^ 2).den : ZMod p)) *
              ((q.num : ZMod p) / (q.den : ZMod p))⁻¹ := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have hvm : padicValRat p (m : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hm0 hm)]
    norm_num
  have ha : ((2 / (m : ℚ) ^ 2).den : ZMod p) ≠ 0 := by
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [padicValRat.div (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 2 hmq),
      padicValRat.pow, hvm]
    simpa using zero_le_padicValRat_of_nat (p := p) 2
  have hi := rational_residue_inv hq hv
  have hprod := rational_residue_mul ha hi.1
  have heq : (2 / (m : ℚ) ^ 2) * q⁻¹ = 2 / ((m : ℚ) ^ 2 * q) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, hi.2] at hprod
  exact hprod

theorem boundaryPlusWeight_even_multiple_reduction {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm0 : 0 < m) (hmEven : m % 2 = 0) (hm : m < p) :
    (((p : ℚ) ^ 2 * boundaryPlusWeight (p * m)).den : ZMod p) ≠ 0 ∧
      ((boundaryPlusWeight m).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryPlusWeight (p * m)).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryPlusWeight (p * m)).den : ZMod p) =
            ((boundaryPlusWeight m).num : ZMod p) /
              ((boundaryPlusWeight m).den : ZMod p) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have hEven : (p * m) % 2 = 0 := by simp [Nat.mul_mod, hmEven]
  have hsmall : p * m < p ^ 2 := by nlinarith [hp.out.pos]
  have hrem : (p * m) % p = 0 := by simp
  have hdiv : (p * m) / p = m := by simp [hp.out.ne_zero]
  have hH : R (boundaryFactor (p * m)) = R (boundaryFactor m) := by
    have h := boundaryFactor_even_digit_reduction hp2 hEven
      (show ((p * m) % p) % 2 = 0 by rw [hrem])
    simpa [R, hrem, hdiv] using h.2.2.2
  have hvH : padicValRat p (boundaryFactor (p * m)) = 0 := by
    rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 hEven hsmall, hrem]
    norm_num
  have hi := two_div_square_mul_residue hm0 hm (boundaryFactor_ne_zero (p * m)) hvH
  have hj := two_div_square_mul_residue hm0 hm (boundaryFactor_ne_zero m)
    (boundaryFactor_small_valuation_zero hp2 hm)
  have heq : (p : ℚ) ^ 2 * boundaryPlusWeight (p * m) =
      2 / ((m : ℚ) ^ 2 * boundaryFactor (p * m)) := by
    rw [boundaryPlusWeight, Nat.cast_mul]
    field_simp [hpq, hmq, boundaryFactor_ne_zero (p * m)]
  refine ⟨?_, boundaryPlusWeight_small_den_ne_zero hp2 hm0 hm, ?_⟩
  · simpa only [heq] using hi.1
  · rw [heq]
    change R (2 / ((m : ℚ) ^ 2 * boundaryFactor (p * m))) =
      R (2 / ((m : ℚ) ^ 2 * boundaryFactor m))
    have hiR : R (2 / ((m : ℚ) ^ 2 * boundaryFactor (p * m))) =
        R (2 / (m : ℚ) ^ 2) * (R (boundaryFactor (p * m)))⁻¹ := hi.2
    have hjR : R (2 / ((m : ℚ) ^ 2 * boundaryFactor m)) =
        R (2 / (m : ℚ) ^ 2) * (R (boundaryFactor m))⁻¹ := hj.2
    rw [hiR, hjR, hH]

theorem boundaryPlusWeight_odd_multiple_reduction {p m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hmOdd : m % 2 = 1) (hm : m < p) :
    (((p : ℚ) * boundaryPlusWeight (p * m)).den : ZMod p) ≠ 0 ∧
      ((boundaryPlusWeight m).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * boundaryPlusWeight (p * m)).num : ZMod p) /
          (((p : ℚ) * boundaryPlusWeight (p * m)).den : ZMod p) =
            (-1 : ZMod p) ^ ((p - 1) / 2) *
              (((boundaryPlusWeight m).num : ZMod p) /
                ((boundaryPlusWeight m).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hm0 : 0 < m := by omega
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
  have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hOdd : (p * m) % 2 = 1 := by simp [Nat.mul_mod, hpOdd, hmOdd]
  have hsmall : p * m < p ^ 2 := by nlinarith [hp.out.pos]
  have hrem : (p * m) % p = 0 := by simp
  have hH : R ((p : ℚ) * boundaryFactor (p * m)) =
      (-1 : ZMod p) ^ ((p - 1) / 2) * R (boundaryFactor m) := by
    simpa only [Nat.mul_comm] using
      (boundaryFactor_odd_multiple_reduction hp2 hmOdd hm).2.2
  have hvH : padicValRat p ((p : ℚ) * boundaryFactor (p * m)) = 0 := by
    rw [padicValRat.mul hpq (boundaryFactor_ne_zero (p * m)),
      padicValRat.self hp.out.one_lt,
      boundaryFactor_odd_prime_valuation hp.out hp2 hOdd hsmall, hrem]
    norm_num
  have hi := two_div_square_mul_residue hm0 hm
    (mul_ne_zero hpq (boundaryFactor_ne_zero (p * m))) hvH
  have hj := two_div_square_mul_residue hm0 hm (boundaryFactor_ne_zero m)
    (boundaryFactor_small_valuation_zero hp2 hm)
  have heq : (p : ℚ) * boundaryPlusWeight (p * m) =
      2 / ((m : ℚ) ^ 2 * ((p : ℚ) * boundaryFactor (p * m))) := by
    rw [boundaryPlusWeight, Nat.cast_mul]
    field_simp [hpq, hmq, boundaryFactor_ne_zero (p * m)]
  refine ⟨?_, boundaryPlusWeight_small_den_ne_zero hp2 hm0 hm, ?_⟩
  · simpa only [heq] using hi.1
  · rw [heq]
    change R (2 / ((m : ℚ) ^ 2 * ((p : ℚ) * boundaryFactor (p * m)))) =
      (-1 : ZMod p) ^ ((p - 1) / 2) * R (2 / ((m : ℚ) ^ 2 * boundaryFactor m))
    have hiR : R (2 / ((m : ℚ) ^ 2 * ((p : ℚ) * boundaryFactor (p * m)))) =
        R (2 / (m : ℚ) ^ 2) * (R ((p : ℚ) * boundaryFactor (p * m)))⁻¹ := hi.2
    have hjR : R (2 / ((m : ℚ) ^ 2 * boundaryFactor m)) =
        R (2 / (m : ℚ) ^ 2) * (R (boundaryFactor m))⁻¹ := hj.2
    rw [hiR, hjR, hH]
    simp only [mul_inv_rev]
    ring_nf
    norm_num





def momentScalarPred (z : ℕ) : ℚ :=
  if z = 0 then 0 else momentScalar (z - 1)

@[simp] theorem momentScalarPred_zero : momentScalarPred 0 = 0 := by
  simp [momentScalarPred]

theorem momentScalarPred_of_odd {z : ℕ} (hz : z % 2 = 1) :
    momentScalarPred z = 2 * boundaryFactor z := by
  have heq : z = 2 * (z / 2) + 1 := by omega
  generalize z / 2 = l at heq
  subst z
  rw [momentScalarPred, ite_eq_right (by omega : 2 * l + 1 ≠ 0),
    show 2 * l + 1 - 1 = 2 * l by omega, momentScalar_even, boundaryFactor_odd]
  ring

theorem momentScalarPred_of_even {z : ℕ} (hz : z % 2 = 0) :
    momentScalarPred z = 0 := by
  by_cases hzero : z = 0
  · simp [hzero]
  · have hprev : (z - 1) % 2 ≠ 0 := by omega
    simp [momentScalarPred, hzero, momentScalar, hprev]

theorem momentScalarPred_small_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : z < p) :
    0 ≤ padicValRat p (momentScalarPred z) := by
  by_cases hzero : z = 0
  · simp [hzero]
  · rw [momentScalarPred, ite_eq_right hzero]
    exact momentScalar_odd_prime_valuation_nonneg hp hp2 (by omega)

theorem momentScalarPred_scaled_valuation_nonneg {p z : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : z < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) * momentScalarPred z) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases heven : z % 2 = 0
  · simp [momentScalarPred_of_even heven]
  · have hodd : z % 2 = 1 := by omega
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hv := boundaryFactor_odd_scaled_valuation_nonneg hp hp2 hodd hz
    have htwo : 0 ≤ padicValRat p (2 : ℚ) := zero_le_padicValRat_of_nat 2
    rw [momentScalarPred_of_odd hodd,
      show (p : ℚ) * (2 * boundaryFactor z) = 2 * ((p : ℚ) * boundaryFactor z) by ring,
      padicValRat.mul (by norm_num) (mul_ne_zero hpq (boundaryFactor_ne_zero z))]
    omega

theorem momentScalarPred_prime_digit_reduction {p z : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hz : z < p ^ 2) :
    (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 ∧
      ((momentScalarPred (z / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) * momentScalarPred z).num : ZMod p) /
          (((p : ℚ) * momentScalarPred z).den : ZMod p) =
            (oddPrimeWeight p).coeff (p - 1 - z % p) *
              (((momentScalarPred (z / p)).num : ZMod p) /
                ((momentScalarPred (z / p)).den : ZMod p)) := by
  have hP : z / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [pow_two] using hz)
  have hr : z % p < p := Nat.mod_lt _ hp.out.pos
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div z p)
  simp only [Nat.add_mod, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod] at hpar
  have hscaled : (((p : ℚ) * momentScalarPred z).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (momentScalarPred_scaled_valuation_nonneg hp.out hp2 hz)
  have hsmall : ((momentScalarPred (z / p)).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (momentScalarPred_small_valuation_nonneg hp.out hp2 hP)
  refine ⟨hscaled, hsmall, ?_⟩
  by_cases hzEven : z % 2 = 0
  · by_cases hrEven : (z % p) % 2 = 0
    · have hPEven : (z / p) % 2 = 0 := by omega
      rw [momentScalarPred_of_even hzEven, momentScalarPred_of_even hPEven]
      norm_num
    · have hEzero : (oddPrimeWeight p).coeff (p - 1 - z % p) = 0 := by
        rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
          oddPrimeWeight_coeff_odd p (z % p) hrEven, mul_zero]
      rw [momentScalarPred_of_even hzEven, hEzero]
      norm_num
  · have hzOdd : z % 2 = 1 := by omega
    by_cases hrEven : (z % p) % 2 = 0
    · have hPOdd : (z / p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_even_remainder_reduction hp2 hzOdd hz hrEven
      have hleft :
          (((p : ℚ) * momentScalarPred z).num : ZMod p) /
              (((p : ℚ) * momentScalarPred z).den : ZMod p) =
            2 * ((((p : ℚ) * boundaryFactor z).num : ZMod p) /
              (((p : ℚ) * boundaryFactor z).den : ZMod p)) := by
        have h := rational_residue_nat_mul_eq 1 2 hscaled hH.1
          (by rw [momentScalarPred_of_odd hzOdd]; ring)
        simpa only [Nat.cast_one, one_mul, Nat.cast_ofNat] using h
      have hright :
          ((momentScalarPred (z / p)).num : ZMod p) /
              ((momentScalarPred (z / p)).den : ZMod p) =
            2 * (((boundaryFactor (z / p)).num : ZMod p) /
              ((boundaryFactor (z / p)).den : ZMod p)) := by
        have h := rational_residue_nat_mul_eq 1 2 hsmall hH.2.1
          (by rw [momentScalarPred_of_odd hPOdd]; ring)
        simpa only [Nat.cast_one, one_mul, Nat.cast_ofNat] using h
      have hrem : 2 * ((z % p) / 2) = z % p := by omega
      have hcoeff : (oddPrimeWeight p).coeff (z % p) =
          ((centralCoeff ((z % p) / 2)).num : ZMod p) /
            ((centralCoeff ((z % p) / 2)).den : ZMod p) := by
        calc
          (oddPrimeWeight p).coeff (z % p) =
              (oddPrimeWeight p).coeff (2 * ((z % p) / 2)) := by rw [hrem]
          _ = ((2 * ((z % p) / 2)).choose ((z % p) / 2) : ZMod p) /
              (4 : ZMod p) ^ ((z % p) / 2) :=
            oddPrimeWeight_coeff_central hp2 (by omega)
          _ = _ := (centralCoeff_reduced_residue hp2 ((z % p) / 2)).2.symm
      rw [hleft, hH.2.2.2, oddPrimeWeight_coeff_reverse hp.out hp2 hr, hcoeff, hright]
      ring
    · have hrOdd : (z % p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_odd_remainder_reduction hp2 hzOdd hz hrOdd
      have hleft :
          (((p : ℚ) * momentScalarPred z).num : ZMod p) /
              (((p : ℚ) * momentScalarPred z).den : ZMod p) = 0 := by
        have h := rational_residue_nat_mul_eq 1 2 hscaled hH.1
          (by rw [momentScalarPred_of_odd hzOdd]; ring)
        simpa only [Nat.cast_one, one_mul, Nat.cast_ofNat, hH.2, mul_zero] using h
      have hEzero : (oddPrimeWeight p).coeff (p - 1 - z % p) = 0 := by
        rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
          oddPrimeWeight_coeff_odd p (z % p) hrEven, mul_zero]
      rw [hleft, hEzero, zero_mul]





open scoped BigOperators

theorem boundaryMinus_odd_explicit {u : ℕ} (huOdd : u % 2 = 1) :
    boundaryMinus u = boundaryFactor u * oddHarmonicRat u := by
  rw [boundaryMinus_explicit]
  congr 1
  unfold parityBoundarySum oddHarmonicRat
  apply Finset.sum_congr rfl
  intro z hz
  rw [huOdd]
  split_ifs with h
  · rw [boundaryMinusWeight, ite_eq_right (by omega : z % 2 ≠ 0)]
  · rfl

theorem boundaryMinus_odd_scaled_product {p u : ℕ} (huOdd : u % 2 = 1) :
    (p : ℚ) ^ 2 * boundaryMinus u =
      ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * oddHarmonicRat u) := by
  rw [boundaryMinus_odd_explicit huOdd]
  ring

theorem boundaryMinus_odd_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (huOdd : u % 2 = 1) (hu : u < p ^ 2) :
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
  have hstrip := oddHarmonicRat_prime_digit_reduction hp2 hu
  have hstripR : R ((p : ℚ) * oddHarmonicRat u) = R (oddHarmonicRat (u / p)) :=
    hstrip.2.2
  have hHden := (boundaryFactor_odd_integral_denominators hp2 huOdd hu).2
  have hmul := rational_residue_mul hHden hstrip.1
  have hprod := boundaryMinus_odd_scaled_product (p := p) huOdd
  have hscaled : (((p : ℚ) ^ 2 * boundaryMinus u).den : ZMod p) ≠ 0 ∧
      R ((p : ℚ) ^ 2 * boundaryMinus u) =
        R ((p : ℚ) * boundaryFactor u) * R ((p : ℚ) * oddHarmonicRat u) := by
    simpa only [R, ← hprod] using hmul
  have htarget : ((boundaryMinus (u / p)).den : ZMod p) ≠ 0 :=
    rational_den_ne_zero_of_valuation_nonneg
      (boundaryMinus_odd_prime_valuation_nonneg hp.out hp2 _ hP)
  refine ⟨hscaled.1, htarget, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryMinus u) =
    (oddPrimeWeight p).coeff (p - 1 - u % p) * R (boundaryMinus (u / p))
  rw [hscaled.2, hstripR]
  by_cases hrEven : (u % p) % 2 = 0
  · have hH := boundaryFactor_odd_even_remainder_reduction hp2 huOdd hu hrEven
    have hHR : R ((p : ℚ) * boundaryFactor u) =
        (-1 : ZMod p) ^ ((p - 1) / 2) * R (centralCoeff ((u % p) / 2)) *
          R (boundaryFactor (u / p)) := hH.2.2.2
    have hpOdd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
    have hdecomp := Nat.mod_add_div u p
    have hpar := congrArg (fun n : ℕ => n % 2) hdecomp
    simp only [Nat.add_mod, Nat.mul_mod, hrEven, hpOdd, zero_add, one_mul,
      Nat.mod_mod, huOdd] at hpar
    have hB := rational_residue_mul hH.2.1 hstrip.2.1
    have hBres : R (boundaryMinus (u / p)) =
        R (boundaryFactor (u / p)) * R (oddHarmonicRat (u / p)) := by
      rw [boundaryMinus_odd_explicit hpar]
      exact hB.2
    have hrEq : 2 * ((u % p) / 2) = u % p := by omega
    have hc : R (centralCoeff ((u % p) / 2)) = (oddPrimeWeight p).coeff (u % p) := by
      change ((centralCoeff ((u % p) / 2)).num : ZMod p) /
        ((centralCoeff ((u % p) / 2)).den : ZMod p) = _
      rw [(centralCoeff_reduced_residue hp2 ((u % p) / 2)).2]
      symm
      simpa only [hrEq] using
        (oddPrimeWeight_coeff_central hp2 (show 2 * ((u % p) / 2) < p by omega))
    rw [hHR, oddPrimeWeight_coeff_reverse hp.out hp2 hr, ← hc, hBres]
    ring
  · have hrOdd : (u % p) % 2 = 1 := by omega
    have hH := boundaryFactor_odd_odd_remainder_reduction hp2 huOdd hu hrOdd
    have hHR : R ((p : ℚ) * boundaryFactor u) = 0 := hH.2
    have hcoeff : (oddPrimeWeight p).coeff (p - 1 - u % p) = 0 := by
      rw [oddPrimeWeight_coeff_reverse hp.out hp2 hr,
        oddPrimeWeight_coeff_odd p (u % p) hrEven, mul_zero]
    rw [hHR, hcoeff, zero_mul, zero_mul]

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

def boundaryPlusParitySum (e u : ℕ) : ℚ :=
  ∑ z ∈ Finset.range (u + 1), if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0

@[simp] theorem boundaryPlusParitySum_zero (e : ℕ) : boundaryPlusParitySum e 0 = 0 := by
  simp [boundaryPlusParitySum]

theorem boundaryPlusParitySum_succ (e u : ℕ) :
    boundaryPlusParitySum e (u + 1) = boundaryPlusParitySum e u +
      (if 0 < u + 1 ∧ (u + 1) % 2 = e then boundaryPlusWeight (u + 1) else 0) := by
  simp only [boundaryPlusParitySum, Finset.sum_range_succ]

theorem boundaryPlusParitySum_eq (u : ℕ) :
    boundaryPlusParitySum (u % 2) u = parityBoundarySum boundaryPlusWeight u := rfl

theorem boundaryPlusParitySum_small_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (e : ℕ) (hu : u < p) :
    ((boundaryPlusParitySum e u).den : ZMod p) ≠ 0 := by
  unfold boundaryPlusParitySum
  apply (rational_residue_sum _ _ ?_).1
  intro z hz
  by_cases hgood : 0 < z ∧ z % 2 = e
  · rw [ite_eq_left hgood]
    exact boundaryPlusWeight_small_den_ne_zero hp2 hgood.1
      (by have := Finset.mem_range.mp hz; omega)
  · simp [hgood]

private theorem plusParityTerm_scaled_nonmultiple {p z e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (he : e ≤ 1) (hz0 : 0 < z) (hz : z < p ^ 2) (hnon : ¬p ∣ z) :
    (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
      (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) ≠ 0 ∧
      (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
        (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).num : ZMod p) /
        (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
          (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) = 0 := by
  by_cases hgood : 0 < z ∧ z % 2 = e
  · rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · simpa only [ite_eq_left hgood, ite_eq_left rfl, ite_true] using
        boundaryPlusWeight_even_nonmultiple_reduction hp2 hz0 hgood.2 hz hnon
    · simpa only [ite_eq_left hgood, show (1 : ℕ) ≠ 0 by decide, ite_false] using
        boundaryPlusWeight_odd_nonmultiple_reduction hp2 hgood.2 hz hnon
  · simp [hgood]

private theorem plusParityTerm_scaled_multiple {p z e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (he : e ≤ 1) (hz0 : 0 < z) (hz : z < p ^ 2) (hdiv : p ∣ z) :
    (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
      (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) ≠ 0 ∧
      ((if 0 < z / p ∧ (z / p) % 2 = e then boundaryPlusWeight (z / p) else 0).den : ZMod p) ≠ 0 ∧
        (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
          (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).num : ZMod p) /
          (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
            (if 0 < z ∧ z % 2 = e then boundaryPlusWeight z else 0)).den : ZMod p) =
              (if e = 0 then 1 else (-1 : ZMod p) ^ ((p - 1) / 2)) *
                (((if 0 < z / p ∧ (z / p) % 2 = e then boundaryPlusWeight (z / p) else 0).num : ZMod p) /
                  ((if 0 < z / p ∧ (z / p) % 2 = e then boundaryPlusWeight (z / p) else 0).den : ZMod p)) := by
  have heq : z = p * (z / p) := (Nat.mul_div_cancel' hdiv).symm
  have hq0 : 0 < z / p := by
    by_contra hn
    have hzq : z / p = 0 := Nat.eq_zero_of_not_pos hn
    rw [hzq, mul_zero] at heq
    omega
  have hq : z / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hz)
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar : z % 2 = (z / p) % 2 := by
    conv_lhs => rw [heq, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod]
  by_cases hgood : 0 < z ∧ z % 2 = e
  · have hqgood : 0 < z / p ∧ (z / p) % 2 = e := ⟨hq0, hpar ▸ hgood.2⟩
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · have h := boundaryPlusWeight_even_multiple_reduction hp2 hq0 hqgood.2 hq
      rw [← heq] at h
      simpa only [ite_eq_left hgood, ite_eq_left hqgood, ite_eq_left rfl, ite_true, one_mul] using h
    · have h := boundaryPlusWeight_odd_multiple_reduction hp2 hqgood.2 hq
      rw [← heq] at h
      simpa only [ite_eq_left hgood, ite_eq_left hqgood, show (1 : ℕ) ≠ 0 by decide, ite_false] using h
  · have hqbad : ¬(0 < z / p ∧ (z / p) % 2 = e) := by
      intro h
      exact hgood ⟨hz0, hpar.trans h.2⟩
    simp only [ite_eq_right hgood, ite_eq_right hqbad, mul_zero]
    norm_num

theorem boundaryPlusParitySum_prime_digit_reduction {p u e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (he : e ≤ 1) (hu : u < p ^ 2) :
    (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u).den : ZMod p) ≠ 0 ∧
      ((boundaryPlusParitySum e (u / p)).den : ZMod p) ≠ 0 ∧
        (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u).num : ZMod p) /
          (((if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u).den : ZMod p) =
            (if e = 0 then 1 else (-1 : ZMod p) ^ ((p - 1) / 2)) *
              (((boundaryPlusParitySum e (u / p)).num : ZMod p) /
                ((boundaryPlusParitySum e (u / p)).den : ZMod p)) := by
  revert hu
  induction u with
  | zero => intro hu; simp
  | succ u ih =>
    intro hu
    have hprev := ih (by omega : u < p ^ 2)
    have hscale :
        (if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e (u + 1) =
          (if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) * boundaryPlusParitySum e u +
            (if e = 0 then (p : ℚ) ^ 2 else (p : ℚ)) *
              (if 0 < u + 1 ∧ (u + 1) % 2 = e then boundaryPlusWeight (u + 1) else 0) := by
      rw [boundaryPlusParitySum_succ, mul_add]
    by_cases hdiv : p ∣ u + 1
    · have hquot : (u + 1) / p = u / p + 1 := Nat.succ_div_of_dvd hdiv
      have hterm := plusParityTerm_scaled_multiple hp2 he (by omega : 0 < u + 1) hu hdiv
      rw [hquot] at hterm
      have hl := rational_residue_add hprev.1 hterm.1
      have hr := rational_residue_add hprev.2.1 hterm.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot, boundaryPlusParitySum_succ]
        exact hr.1
      · rw [hscale, hl.2, hprev.2.2, hterm.2.2, hquot, boundaryPlusParitySum_succ, hr.2]
        ring
    · have hquot : (u + 1) / p = u / p := Nat.succ_div_of_not_dvd hdiv
      have hterm := plusParityTerm_scaled_nonmultiple hp2 he (by omega : 0 < u + 1) hu hdiv
      have hl := rational_residue_add hprev.1 hterm.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hquot]
        exact hprev.2.1
      · rw [hscale, hl.2, hterm.2, add_zero, hquot]
        exact hprev.2.2

end InternalCatalan



namespace InternalCatalan

private theorem plus_start_small_H_den {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p) : ((boundaryFactor u).den : ZMod p) ≠ 0 := by
  apply rational_den_ne_zero_of_valuation_nonneg
  have hu2 : u < p ^ 2 := by nlinarith [hp.out.two_le]
  by_cases he : u % 2 = 0
  · rw [boundaryFactor_even_odd_prime_valuation hp.out hp2 he hu2,
      Nat.mod_eq_of_lt hu]
    simp [he]
  · rw [boundaryFactor_odd_prime_valuation hp.out hp2 (by omega) hu2,
      Nat.mod_eq_of_lt hu]
    simp [he]

theorem boundaryPlus_small_successor_den_ne_zero {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p) : ((boundaryPlus (u + 1)).den : ZMod p) ≠ 0 := by
  rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq]
  exact (rational_residue_mul (plus_start_small_H_den hp2 hu)
    (boundaryPlusParitySum_small_den_ne_zero hp2 (u % 2) hu)).1

theorem boundaryPlus_prime_digit_reduction {p u : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hu : u < p ^ 2) :
    (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).den : ZMod p) ≠ 0 ∧
      ((boundaryPlus (u / p + 1)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).num : ZMod p) /
          (((p : ℚ) ^ 2 * boundaryPlus (u + 1)).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((boundaryPlus (u / p + 1)).num : ZMod p) /
                ((boundaryPlus (u / p + 1)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  have hP : u / p < p :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hu)
  have hr : u % p < p := Nat.mod_lt _ hp.out.pos
  have hpOdd := hp.out.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpar := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div u p)
  simp only [Nat.add_mod, Nat.mul_mod, hpOdd, one_mul, Nat.mod_mod] at hpar
  have hcoeff (hrEven : (u % p) % 2 = 0) :
      (oddPrimeWeight p).coeff (u % p) = R (centralCoeff ((u % p) / 2)) := by
    have hrem : 2 * ((u % p) / 2) = u % p := by omega
    calc
      (oddPrimeWeight p).coeff (u % p) =
          (oddPrimeWeight p).coeff (2 * ((u % p) / 2)) := by rw [hrem]
      _ = ((2 * ((u % p) / 2)).choose ((u % p) / 2) : ZMod p) /
          (4 : ZMod p) ^ ((u % p) / 2) := oddPrimeWeight_coeff_central hp2 (by omega)
      _ = _ := (centralCoeff_reduced_residue hp2 ((u % p) / 2)).2.symm
  refine ⟨boundaryPlus_prime_sq_scaled_den_ne_zero hp2 hu,
    boundaryPlus_small_successor_den_ne_zero hp2 hP, ?_⟩
  change R ((p : ℚ) ^ 2 * boundaryPlus (u + 1)) =
    (oddPrimeWeight p).coeff (u % p) * R (boundaryPlus (u / p + 1))
  by_cases huEven : u % 2 = 0
  · have hstrip := boundaryPlusParitySum_prime_digit_reduction (e := 0) hp2 (by decide) hu
    simp only [ite_true, one_mul] at hstrip
    have hbig : (p : ℚ) ^ 2 * boundaryPlus (u + 1) =
        boundaryFactor u * ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) := by
      rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, huEven]
      ring
    by_cases hrEven : (u % p) % 2 = 0
    · have hPEven : (u / p) % 2 = 0 := by omega
      have hH := boundaryFactor_even_digit_reduction hp2 huEven hrEven
      have hbigR : R (boundaryFactor u * ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u)) =
          R (boundaryFactor u) * R ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hsmall : boundaryPlus (u / p + 1) =
          boundaryFactor (u / p) * boundaryPlusParitySum 0 (u / p) := by
        rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, hPEven]
      have hsmallR : R (boundaryPlus (u / p + 1)) =
          R (boundaryFactor (u / p)) * R (boundaryPlusParitySum 0 (u / p)) := by
        rw [hsmall]
        exact (rational_residue_mul hH.2.1 hstrip.2.1).2
      have hHR : R (boundaryFactor u) =
          R (boundaryFactor (u / p)) * R (centralCoeff ((u % p) / 2)) := hH.2.2.2
      have hstripR : R ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) =
          R (boundaryPlusParitySum 0 (u / p)) := hstrip.2.2
      rw [hbig, hbigR, hHR, hstripR, hcoeff hrEven, hsmallR]
      ring
    · have hrOdd : (u % p) % 2 = 1 := by omega
      have hH := boundaryFactor_even_carry_reduction hp2 huEven hu hrOdd
      have hbigR : R (boundaryFactor u * ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u)) =
          R (boundaryFactor u) * R ((p : ℚ) ^ 2 * boundaryPlusParitySum 0 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hHR : R (boundaryFactor u) = 0 := hH.2
      rw [hbig, hbigR, hHR, oddPrimeWeight_coeff_odd p (u % p) hrEven, zero_mul, zero_mul]
  · have huOdd : u % 2 = 1 := by omega
    have hstrip := boundaryPlusParitySum_prime_digit_reduction (e := 1) hp2 (by decide) hu
    simp only [show (1 : ℕ) ≠ 0 by decide, ite_false] at hstrip
    have hbig : (p : ℚ) ^ 2 * boundaryPlus (u + 1) =
        ((p : ℚ) * boundaryFactor u) * ((p : ℚ) * boundaryPlusParitySum 1 u) := by
      rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, huOdd]
      ring
    by_cases hrEven : (u % p) % 2 = 0
    · have hPOdd : (u / p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_even_remainder_reduction hp2 huOdd hu hrEven
      have hbigR : R (((p : ℚ) * boundaryFactor u) * ((p : ℚ) * boundaryPlusParitySum 1 u)) =
          R ((p : ℚ) * boundaryFactor u) * R ((p : ℚ) * boundaryPlusParitySum 1 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hsmall : boundaryPlus (u / p + 1) =
          boundaryFactor (u / p) * boundaryPlusParitySum 1 (u / p) := by
        rw [boundaryPlus_explicit, ← boundaryPlusParitySum_eq, hPOdd]
      have hsmallR : R (boundaryPlus (u / p + 1)) =
          R (boundaryFactor (u / p)) * R (boundaryPlusParitySum 1 (u / p)) := by
        rw [hsmall]
        exact (rational_residue_mul hH.2.1 hstrip.2.1).2
      have hHR : R ((p : ℚ) * boundaryFactor u) =
          (-1 : ZMod p) ^ ((p - 1) / 2) * R (centralCoeff ((u % p) / 2)) *
            R (boundaryFactor (u / p)) := hH.2.2.2
      have hstripR : R ((p : ℚ) * boundaryPlusParitySum 1 u) =
          (-1 : ZMod p) ^ ((p - 1) / 2) * R (boundaryPlusParitySum 1 (u / p)) := hstrip.2.2
      have heps : ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm ((p - 1) / 2) 2, pow_mul]
        norm_num
      rw [hbig, hbigR, hHR, hstripR, hcoeff hrEven, hsmallR]
      calc
        _ = ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ 2 *
            (R (centralCoeff ((u % p) / 2)) *
              (R (boundaryFactor (u / p)) * R (boundaryPlusParitySum 1 (u / p)))) := by ring
        _ = _ := by rw [heps, one_mul]
    · have hrOdd : (u % p) % 2 = 1 := by omega
      have hH := boundaryFactor_odd_odd_remainder_reduction hp2 huOdd hu hrOdd
      have hbigR : R (((p : ℚ) * boundaryFactor u) * ((p : ℚ) * boundaryPlusParitySum 1 u)) =
          R ((p : ℚ) * boundaryFactor u) * R ((p : ℚ) * boundaryPlusParitySum 1 u) :=
        (rational_residue_mul hH.1 hstrip.1).2
      have hHR : R ((p : ℚ) * boundaryFactor u) = 0 := hH.2
      rw [hbig, hbigR, hHR, oddPrimeWeight_coeff_odd p (u % p) hrEven, zero_mul, zero_mul]

end InternalCatalan

end OAI
