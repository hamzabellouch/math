import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeBlockGathering
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeCentralZeta
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeGeneralExtraction
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLowerMomentDigits
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeResidueGathering
import OAI.NumberTheory.Catalan.Estimates.PalindromicExtractedEntries

namespace OAI

section

open scoped BigOperators

namespace InternalCatalan

theorem centralCoeffKernel_odd_prime_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (d : ℤ) :
    ((centralCoeffKernel d).den : ZMod p) ≠ 0 := by
  unfold centralCoeffKernel
  split_ifs with hd
  · exact (centralCoeff_reduced_residue hp2 (d.toNat / 2)).1
  · simp

theorem rawCatalanCoeffRat_odd_prime_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (N r j : ℕ) :
    ((rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 := by
  unfold rawCatalanCoeffRat
  apply (rational_residue_sum (p := p) (Finset.range (H N))
    (fun i => ((rowP N r).coeff i : ℚ) *
      (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) ?_).1
  intro i hi
  have hkernel := centralCoeffKernel_odd_prime_den_ne_zero hp2 ((i : ℤ) - (j : ℤ))
  have hfour := rational_residue_mul (a := (4 : ℚ)) (by norm_num) hkernel
  exact (rational_residue_mul (a := ((rowP N r).coeff i : ℚ)) (by simp) hfour.1).1

theorem rawCatalanTerm_prime_sq_reduction {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) (N r j : ℕ) :
    (((p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0 := by
  have hpz := rational_residue_mul (a := ((p ^ 2 : ℕ) : ℚ)) (b := z) (by simp) hz
  have hfull := rational_residue_mul hpz.1
    (rawCatalanCoeffRat_odd_prime_den_ne_zero hp2 N r j)
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_pow] using hfull.1
  · have hzero :
        ((((p ^ 2 : ℕ) : ℚ) * z * rawCatalanCoeffRat N r j).num : ZMod p) /
          ((((p ^ 2 : ℕ) : ℚ) * z * rawCatalanCoeffRat N r j).den : ZMod p) = 0 := by
      rw [hfull.2, hpz.2]
      simp
    simpa only [Nat.cast_pow] using hzero

end InternalCatalan

end


namespace InternalCatalan

theorem momentUpperStrip_term_zero {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : j + 1 < p ^ 2) (hnd : ¬p ∣ j + 1) :
    (((p : ℚ) ^ 2 *
      (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 *
        (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
        (((p : ℚ) ^ 2 *
          (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) = 0 := by
  have hz : (j + 1) - (u + 1) < p ^ 2 :=
    lt_of_le_of_lt (Nat.sub_le (j + 1) (u + 1)) hb
  have hs := momentScalarPred_prime_digit_reduction hp2 hz
  have hj : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hnd ((ZMod.natCast_eq_zero_iff (j + 1) p).mp hzero)
  have hf := nat_fraction_reduced_residue p (j + 1) hj
  have hm := rational_residue_mul hs.1 hf.1
  have heq : (p : ℚ) ^ 2 *
      (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ)) =
      ((p : ℚ) * momentScalarPred ((j + 1) - (u + 1))) *
        ((p : ℚ) / ((j + 1 : ℕ) : ℚ)) := by ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hm.1
  · rw [heq, hm.2, hf.2]
    simp

theorem momentUpperStrip_term_multiple {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hb : j + 1 < p ^ 2) (hd : p ∣ j + 1) :
    (((p : ℚ) ^ 2 *
      (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) ≠ 0 ∧
      ((momentScalarPred ((j / p + 1) - (u / p + 1)) /
        ((j / p + 1 : ℕ) : ℚ)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 *
          (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).num : ZMod p) /
          (((p : ℚ) ^ 2 *
            (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ))).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((momentScalarPred ((j / p + 1) - (u / p + 1)) /
                ((j / p + 1 : ℕ) : ℚ)).num : ZMod p) /
                ((momentScalarPred ((j / p + 1) - (u / p + 1)) /
                  ((j / p + 1 : ℕ) : ℚ)).den : ZMod p)) := by
  have hsucc : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hd
  have hjmul : j + 1 = p * (j / p + 1) := by
    rw [← hsucc]
    exact (Nat.mul_div_cancel' hd).symm
  by_cases hzero : j + 1 ≤ u + 1
  · have huquot : (u + 1) / p ≤ u / p + 1 := by
      rw [Nat.succ_div]
      split_ifs <;> omega
    have hqle : j / p + 1 ≤ u / p + 1 := by
      have hmono : (j + 1) / p ≤ (u + 1) / p := Nat.div_le_div_right hzero
      rw [hsucc] at hmono
      exact hmono.trans huquot
    simp [Nat.sub_eq_zero_of_le hzero, Nat.sub_eq_zero_of_le hqle]
  · have hactive : u < p * (j / p + 1) := by
      rw [← hjmul]
      omega
    have hquot : ((j + 1) - (u + 1)) / p = (j / p + 1) - (u / p + 1) := by
      rw [hjmul]
      exact Nat.mul_sub_div u p (j / p + 1) hactive
    have hrem : ((j + 1) - (u + 1)) % p = p - (u % p + 1) := by
      rw [hjmul]
      exact Nat.mul_sub_mod hactive
    have hindex : p - 1 - (((j + 1) - (u + 1)) % p) = u % p := by
      rw [hrem]
      have hr : u % p < p := Nat.mod_lt u hp.out.pos
      omega
    have hz : (j + 1) - (u + 1) < p ^ 2 :=
      lt_of_le_of_lt (Nat.sub_le (j + 1) (u + 1)) hb
    have hqsmall : j / p + 1 < p := by
      rw [← hsucc]
      exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa only [pow_two] using hb)
    have hqnot : ¬p ∣ j / p + 1 :=
      Nat.not_dvd_of_pos_of_lt (Nat.succ_pos (j / p)) hqsmall
    have hqden : ((j / p + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hden
      exact hqnot ((ZMod.natCast_eq_zero_iff (j / p + 1) p).mp hden)
    have hf := nat_fraction_reduced_residue 1 (j / p + 1) hqden
    simp only [Nat.cast_one] at hf
    have hs := momentScalarPred_prime_digit_reduction hp2 hz
    have hl := rational_residue_mul hs.1 hf.1
    have hr := rational_residue_mul hs.2.1 hf.1
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hqq : ((j / p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hjcast : ((j + 1 : ℕ) : ℚ) =
        (p : ℚ) * ((j / p + 1 : ℕ) : ℚ) := by exact_mod_cast hjmul
    have hleft : (p : ℚ) ^ 2 *
        (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ)) =
        ((p : ℚ) * momentScalarPred ((j + 1) - (u + 1))) *
          (1 / ((j / p + 1 : ℕ) : ℚ)) := by
      rw [hjcast]
      field_simp [hpq, hqq]
    have hright : momentScalarPred ((j / p + 1) - (u / p + 1)) /
        ((j / p + 1 : ℕ) : ℚ) =
        momentScalarPred (((j + 1) - (u + 1)) / p) *
          (1 / ((j / p + 1 : ℕ) : ℚ)) := by
      rw [hquot]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hleft]
      exact hl.1
    · rw [hright]
      exact hr.1
    · rw [hleft, hl.2, hs.2.2, hindex, hright, hr.2]
      ring





open scoped BigOperators

def momentUpperPrefix (u j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range j,
    momentScalarPred ((k + 1) - (u + 1)) / ((k + 1 : ℕ) : ℚ)

@[simp] theorem momentUpperPrefix_zero (u : ℕ) : momentUpperPrefix u 0 = 0 := by
  simp [momentUpperPrefix]

theorem momentUpperPrefix_succ (u j : ℕ) :
    momentUpperPrefix u (j + 1) = momentUpperPrefix u j +
      momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ) := by
  unfold momentUpperPrefix
  rw [Finset.sum_range_succ]

theorem momentUpperPrefix_of_le {u j : ℕ} (hj : j ≤ u + 1) :
    momentUpperPrefix u j = 0 := by
  unfold momentUpperPrefix
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [Nat.sub_eq_zero_of_le (by omega : k + 1 ≤ u + 1), momentScalarPred_zero, zero_div]

theorem momentRat_upper_prefix (u i : ℕ) :
    momentRat i (u + i + 1) = boundaryPlus (u + 1) - momentUpperPrefix u (u + i + 1) := by
  induction i with
  | zero => simp [momentUpperPrefix_of_le (le_refl (u + 1))]
  | succ i ih =>
    have hrec := momentRat_step i (u + i + 1)
    rw [ih] at hrec
    have hpred : momentScalarPred ((u + i + 1 + 1) - (u + 1)) = momentScalar i := by
      rw [show (u + i + 1 + 1) - (u + 1) = i + 1 by omega]
      simp [momentScalarPred]
    rw [show u + (i + 1) + 1 = (u + i + 1) + 1 by omega,
      momentUpperPrefix_succ, hpred]
    linarith only [hrec]

theorem momentUpperPrefix_prime_digit_reduction {p u j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentUpperPrefix u j).den : ZMod p) ≠ 0 ∧
      ((momentUpperPrefix (u / p) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentUpperPrefix u j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentUpperPrefix u j).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((momentUpperPrefix (u / p) (j / p)).num : ZMod p) /
                ((momentUpperPrefix (u / p) (j / p)).den : ZMod p)) := by
  revert hbound
  induction j with
  | zero => intro hbound; simp
  | succ j ih =>
    intro hbound
    have hprev := ih (by omega : j < p ^ 2)
    have hscale : (p : ℚ) ^ 2 * momentUpperPrefix u (j + 1) =
        (p : ℚ) ^ 2 * momentUpperPrefix u j +
          (p : ℚ) ^ 2 *
            (momentScalarPred ((j + 1) - (u + 1)) / ((j + 1 : ℕ) : ℚ)) := by
      rw [momentUpperPrefix_succ, mul_add]
    by_cases hdiv : p ∣ j + 1
    · have ht := momentUpperStrip_term_multiple (u := u) hp2 hbound hdiv
      have hquot : (j + 1) / p = j / p + 1 := Nat.succ_div_of_dvd hdiv
      have hsmall : momentUpperPrefix (u / p) ((j + 1) / p) =
          momentUpperPrefix (u / p) (j / p) +
            momentScalarPred ((j / p + 1) - (u / p + 1)) /
              ((j / p + 1 : ℕ) : ℚ) := by
        rw [hquot, momentUpperPrefix_succ]
      have hl := rational_residue_add hprev.1 ht.1
      have hr := rational_residue_add hprev.2.1 ht.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hscale]
        exact hl.1
      · rw [hsmall]
        exact hr.1
      · rw [hscale, hl.2, hprev.2.2, ht.2.2, hsmall, hr.2]
        ring
    · have ht := momentUpperStrip_term_zero (u := u) hp2 hbound hdiv
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

def momentRatSigned (i : ℤ) (j : ℕ) : ℚ :=
  if 0 ≤ i then momentRat i.toNat j else
    if i = -1 then momentRatNegOne j else 0

@[simp] theorem momentRatSigned_natCast (i j : ℕ) :
    momentRatSigned (i : ℤ) j = momentRat i j := by
  simp [momentRatSigned]

@[simp] theorem momentRatSigned_neg_one (j : ℕ) :
    momentRatSigned (-1) j = momentRatNegOne j := by
  norm_num [momentRatSigned]

theorem momentRatSigned_upper_prefix {P q : ℕ} (hPq : P ≤ q) :
    momentRatSigned ((q : ℤ) - (P : ℤ) - 1) q =
      boundaryPlus (P + 1) - momentUpperPrefix P q := by
  by_cases heq : P = q
  · subst q
    simp only [sub_self, zero_sub, momentRatSigned_neg_one, momentRatNegOne_eq,
      momentUpperPrefix_of_le (Nat.le_succ P), sub_zero]
  · have hlt : P < q := by omega
    have hcast : ((q - P - 1 : ℕ) : ℤ) = (q : ℤ) - (P : ℤ) - 1 := by omega
    have hindex : P + (q - P - 1) + 1 = q := by omega
    rw [← hcast, momentRatSigned_natCast]
    simpa only [hindex] using momentRat_upper_prefix P (q - P - 1)

theorem momentRat_upper_prime_digit_reduction {p u i : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hbound : u + i + 1 < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i (u + i + 1)).den : ZMod p) ≠ 0 ∧
      ((momentRatSigned ((((u + i + 1) / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) - 1)
        ((u + i + 1) / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i (u + i + 1)).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i (u + i + 1)).den : ZMod p) =
            (oddPrimeWeight p).coeff (u % p) *
              (((momentRatSigned ((((u + i + 1) / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) - 1)
                ((u + i + 1) / p)).num : ZMod p) /
                  ((momentRatSigned ((((u + i + 1) / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) - 1)
                    ((u + i + 1) / p)).den : ZMod p)) := by
  have hstart := boundaryPlus_prime_digit_reduction hp2 (show u < p ^ 2 by omega)
  have hstrip := momentUpperPrefix_prime_digit_reduction (u := u) hp2 hbound
  have hl := rational_residue_sub hstart.1 hstrip.1
  have hr := rational_residue_sub hstart.2.1 hstrip.2.1
  have hleft : (p : ℚ) ^ 2 * momentRat i (u + i + 1) =
      (p : ℚ) ^ 2 * boundaryPlus (u + 1) -
        (p : ℚ) ^ 2 * momentUpperPrefix u (u + i + 1) := by
    rw [momentRat_upper_prefix, mul_sub]
  have hright := momentRatSigned_upper_prefix
    (Nat.div_le_div_right (by omega : u ≤ u + i + 1) : u / p ≤ (u + i + 1) / p)
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl.1
  · rw [hright]
    exact hr.1
  · rw [hleft, hl.2, hstart.2.2, hstrip.2.2, hright, hr.2]
    ring

theorem momentRat_prime_digit_reduction_of_lt {p i j : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hij : i < j) (hj : j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      ((momentRatSigned (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) =
            (oddPrimeWeight p).coeff ((j - i - 1) % p) *
              (((momentRatSigned (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1)
                (j / p)).num : ZMod p) /
                  ((momentRatSigned (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1)
                    (j / p)).den : ZMod p)) := by
  have hindex : j - i - 1 + i + 1 = j := by omega
  simpa only [hindex] using momentRat_upper_prime_digit_reduction hp2
    (show j - i - 1 + i + 1 < p ^ 2 by omega)





theorem momentRat_prime_digit_reduction {p i j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hi : i < p ^ 2) (hj : j < p ^ 2) :
    (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) ≠ 0 ∧
      ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p) ≠ 0 ∧
        (((p : ℚ) ^ 2 * momentRat i j).num : ZMod p) /
          (((p : ℚ) ^ 2 * momentRat i j).den : ZMod p) =
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p)) := by
  by_cases hji : j ≤ i
  · have hd := oddPrimeDigitRemainder_of_le hp.out.pos hji
    have hrow : oddPrimeDigitRow p i j = (((i - j) / p + j / p : ℕ) : ℤ) := by
      rw [oddPrimeDigitRow_of_le hp.out.pos hji, Nat.cast_add]
    simpa only [hd, hrow, momentRatSigned_natCast] using
      momentRat_prime_digit_reduction_of_le hp2 hji hi
  · have hij : i < j := by omega
    simpa only [oddPrimeDigitRemainder_of_lt hp.out.pos hij,
      oddPrimeDigitRow_of_lt hp.out.pos hij] using
        momentRat_prime_digit_reduction_of_lt hp2 hij hj





open scoped BigOperators

theorem rawEntryRat_zero_prime_digit_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hH : H N < p ^ 2) (hj : j < H N) :
    (((p : ℚ) ^ 2 * rawEntryRat 0 N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * rawEntryRat 0 N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * rawEntryRat 0 N r j).den : ZMod p) =
          (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ZMod p) *
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p))) -
            (3 / 2 : ZMod p) *
              ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ZMod p) *
                (if i % p = j % p then
                  ((zetaRat (i / p) (j / p)).num : ZMod p) /
                    ((zetaRat (i / p) (j / p)).den : ZMod p) else 0) := by
  let R : ℚ → ZMod p := fun q => (q.num : ZMod p) / (q.den : ZMod p)
  let fM : ℕ → ℚ := fun i => ((rowP N r).coeff i : ℚ) * ((p : ℚ) ^ 2 * momentRat i j)
  let fZ : ℕ → ℚ := fun i => ((rowD N r).coeff i : ℚ) * ((p : ℚ) ^ 2 * zetaRat i j)
  let A : ℚ := ∑ i ∈ Finset.range (H N), fM i
  let B : ℚ := ∑ i ∈ Finset.range (H N), fZ i
  have hj2 : j < p ^ 2 := hj.trans hH
  have hM (i : ℕ) (hi : i ∈ Finset.range (H N)) :
      ((fM i).den : ZMod p) ≠ 0 ∧
        R (fM i) = ((rowP N r).coeff i : ZMod p) *
          (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
            R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := by
    have hd := momentRat_prime_digit_reduction hp2
      ((Finset.mem_range.mp hi).trans hH) hj2
    have hm := rational_residue_mul (a := ((rowP N r).coeff i : ℚ)) (by simp) hd.1
    refine ⟨hm.1, ?_⟩
    have hmr : R (fM i) = ((rowP N r).coeff i : ZMod p) *
        R ((p : ℚ) ^ 2 * momentRat i j) := by
      simpa [R, fM] using hm.2
    have hdr : R ((p : ℚ) ^ 2 * momentRat i j) =
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
          R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := hd.2.2
    rw [hmr, hdr]
    ring
  have hZ (i : ℕ) (hi : i ∈ Finset.range (H N)) :
      ((fZ i).den : ZMod p) ≠ 0 ∧
        R (fZ i) = ((rowD N r).coeff i : ZMod p) *
          (if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0) := by
    have hd := zetaRat_prime_digit_reduction
      ((Finset.mem_range.mp hi).trans hH) hj2
    have hm := rational_residue_mul (a := ((rowD N r).coeff i : ℚ)) (by simp) hd.1
    refine ⟨hm.1, ?_⟩
    have hmr : R (fZ i) = ((rowD N r).coeff i : ZMod p) *
        R ((p : ℚ) ^ 2 * zetaRat i j) := by
      simpa [R, fZ] using hm.2
    have hdr : R ((p : ℚ) ^ 2 * zetaRat i j) =
        if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0 := hd.2
    rw [hmr, hdr]
  have hA := rational_residue_sum (Finset.range (H N)) fM (fun i hi => (hM i hi).1)
  have hB := rational_residue_sum (Finset.range (H N)) fZ (fun i hi => (hZ i hi).1)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hlt : 2 < p := by have := hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt) hdiv
  have h32 := nat_fraction_reduced_residue (p := p) 3 2 htwo
  have hBprod := rational_residue_mul h32.1 hB.1
  have hdiff := rational_residue_sub hA.1 hBprod.1
  have hAeq : A = (p : ℚ) ^ 2 *
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) * momentRat i j) := by
    dsimp only [A, fM]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B = (p : ℚ) ^ 2 *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j) := by
    dsimp only [B, fZ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit : (p : ℚ) ^ 2 * rawEntryRat 0 N r j = A - (3 / 2 : ℚ) * B := by
    rw [rawEntryRat_zero, hAeq, hBeq]
    ring
  have hAres : R A =
      ∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
          R (momentRatSigned (oddPrimeDigitRow p i j) (j / p)) := by
    calc
      R A = ∑ i ∈ Finset.range (H N), R (fM i) := hA.2
      _ = _ := Finset.sum_congr rfl (fun i hi => (hM i hi).2)
  have hBres : R B =
      ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ZMod p) *
        (if i % p = j % p then R (zetaRat (i / p) (j / p)) else 0) := by
    calc
      R B = ∑ i ∈ Finset.range (H N), R (fZ i) := hB.2
      _ = _ := Finset.sum_congr rfl (fun i hi => (hZ i hi).2)
  have h32R : R (3 / 2 : ℚ) = (3 / 2 : ZMod p) := h32.2
  have hBprodR : R ((3 / 2 : ℚ) * B) = R (3 / 2 : ℚ) * R B := hBprod.2
  have hdiffR : R (A - (3 / 2 : ℚ) * B) = R A - R ((3 / 2 : ℚ) * B) := hdiff.2
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hdiff.1
  · change R ((p : ℚ) ^ 2 * rawEntryRat 0 N r j) = _
    rw [hsplit, hdiffR, hBprodR, h32R, hAres, hBres]

theorem rawEntryRat_prime_digit_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hH : H N < p ^ 2) (hj : j < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r j).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * rawEntryRat z N r j).num : ZMod p) /
        (((p : ℚ) ^ 2 * rawEntryRat z N r j).den : ZMod p) =
          (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ZMod p) *
            (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p i j) *
              (((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).num : ZMod p) /
                ((momentRatSigned (oddPrimeDigitRow p i j) (j / p)).den : ZMod p))) -
            (3 / 2 : ZMod p) *
              ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ZMod p) *
                (if i % p = j % p then
                  ((zetaRat (i / p) (j / p)).num : ZMod p) /
                    ((zetaRat (i / p) (j / p)).den : ZMod p) else 0) := by
  have hzero := rawEntryRat_zero_prime_digit_reduction (p := p) (N := N) (r := r) hp2 hH hj
  have hcat := rawCatalanTerm_prime_sq_reduction hp2 z hz N r j
  have hadd := rational_residue_add hzero.1 hcat.1
  have heq : (p : ℚ) ^ 2 * rawEntryRat z N r j =
      (p : ℚ) ^ 2 * rawEntryRat 0 N r j +
        (p : ℚ) ^ 2 * z * rawCatalanCoeffRat N r j := by
    rw [rawEntryRat_affine]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hadd.1
  · rw [heq, hadd.2, hcat.2, add_zero]
    exact hzero.2

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem filterCoeffRat_prime_den_ne_zero {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat N v).den : ZMod p) ≠ 0 := by
  have heq : filterCoeffRat N v =
      (((-1 : ℤ) ^ v * ((q N).choose v : ℤ) : ℤ) : ℚ) := by
    simp [filterCoeffRat]
  rw [heq, Rat.den_intCast, Nat.cast_one]
  exact one_ne_zero

theorem filteredEntryRat_prime_scaled_residue_sum {p r k : ℕ} [hp : Fact p.Prime]
    (hp260 : 260 < p) (hk : k < n p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * filteredEntryRat z p r k).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * filteredEntryRat z p r k).num : ZMod p) /
        (((p : ℚ) ^ 2 * filteredEntryRat z p r k).den : ZMod p) =
          ∑ v ∈ Finset.range (q p + 1),
            (((filterCoeffRat p v).num : ZMod p) / ((filterCoeffRat p v).den : ZMod p)) *
              ((((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v)).num : ZMod p) /
                (((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun x => (x.num : ZMod p) / (x.den : ZMod p)
  let f : ℕ → ℚ := fun v =>
    filterCoeffRat p v * ((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v))
  have hp2 : p ≠ 2 := by omega
  have hH : H p < p ^ 2 := by
    unfold H
    nlinarith
  have hterm (v : ℕ) (hv : v ∈ Finset.range (q p + 1)) :
      ((f v).den : ZMod p) ≠ 0 ∧
        R (f v) = R (filterCoeffRat p v) *
          R ((p : ℚ) ^ 2 * rawEntryRat z p r (b p + k + v)) := by
    have hv' : v ≤ q p := by have := Finset.mem_range.mp hv; omega
    have hj : b p + k + v < H p := by
      have hjL := rawColumn_lt_L hk hv'
      unfold L H at *
      omega
    have hraw := (rawEntryRat_prime_digit_reduction (p := p) (N := p) (r := r)
      hp2 hH hj z hz).1
    exact rational_residue_mul (p := p) (filterCoeffRat_prime_den_ne_zero (p := p) p v) hraw
  have hsum := rational_residue_sum (p := p) (Finset.range (q p + 1)) f
    (fun v hv => (hterm v hv).1)
  have hscale : (p : ℚ) ^ 2 * filteredEntryRat z p r k =
      ∑ v ∈ Finset.range (q p + 1), f v := by
    rw [filteredEntryRat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [f]
    ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hsum.1
  · change R ((p : ℚ) ^ 2 * filteredEntryRat z p r k) = _
    rw [hscale]
    calc
      _ = ∑ v ∈ Finset.range (q p + 1), R (f v) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun v hv => (hterm v hv).2)

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def oddPrimeExtractedP (p N r ell v : ℕ) : ZMod p :=
  (X * (rowP N r).map (Int.castRingHom (ZMod p)) * oddPrimeWeight p).coeff (v * p + ell)

def oddPrimeExtractedD (p N r ell u : ℕ) : ZMod p :=
  ((rowD N r).coeff (u * p + ell) : ZMod p)

theorem rawEntryRat_general_column_layer {p N r k ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hH : H N < p ^ 2) (hell : ell < p)
    (hj : k * p + ell < H N) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z N r (k * p + ell)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (k * p + ell)) =
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k)) -
      (3 / 2 : ZMod p) * ∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u k) := by
  let P : (ZMod p)[X] := (rowP N r).map (Int.castRingHom (ZMod p))
  have hP : ∀ t, H N ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, rowP_coeff_eq_zero_of_ge hN ht, map_zero]
  have hquot : (k * p + ell) / p = k := by
    rw [Nat.mul_comm k p, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hell, add_zero]
  have hmod : (k * p + ell) % p = ell := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hell]
  have hraw := rawEntryRat_prime_digit_reduction (p := p) (N := N) (r := r)
    hp2 hH hj z hz
  have hpg := oddPrime_P_coefficient_contraction_support (H := H N) (k := k)
    hp.out.pos hell P hP (fun v => palindromicRatResidue p (momentRatSigned v k))
  have hcast (a : ℤ) : (Int.castRingHom (ZMod p)) a = (a : ZMod p) := rfl
  have hpg' :
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell)) *
        palindromicRatResidue p (momentRatSigned (oddPrimeDigitRow p t (k * p + ell)) k)) =
      ∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k) := by
    simpa only [P, coeff_map, oddPrimeExtractedP, hcast] using hpg
  have hdg := oddPrime_residue_sum_gather hp.out.pos hell
    (fun t => ((rowD N r).coeff t : ZMod p))
    (fun u => palindromicRatResidue p (zetaRat u k))
    (fun t ht => by rw [rowD_coeff_eq_zero_of_ge hN ht, Int.cast_zero])
  have hdg' :
      (∑ t ∈ Finset.range (H N), ((rowD N r).coeff t : ZMod p) *
        (if t % p = ell then palindromicRatResidue p (zetaRat (t / p) k) else 0)) =
      ∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u k) := by
    simpa only [mul_ite, mul_zero, oddPrimeExtractedD] using hdg
  refine ⟨hraw.1, ?_⟩
  have hres :
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (k * p + ell)) =
      (∑ t ∈ Finset.range (H N), ((rowP N r).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell)) *
        palindromicRatResidue p (momentRatSigned (oddPrimeDigitRow p t (k * p + ell)) k)) -
      (3 / 2 : ZMod p) *
        ∑ t ∈ Finset.range (H N), ((rowD N r).coeff t : ZMod p) *
          (if t % p = ell then palindromicRatResidue p (zetaRat (t / p) k) else 0) := by
    simpa only [palindromicRatResidue, hquot, hmod] using hraw.2
  rw [hres, hpg', hdg']

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_P_digit_contraction {p r0 : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hr : r0 < 48) (i ell : Fin p) (k : ℕ) :
    (∑ t ∈ Finset.range (65 * p), ((rowP p (p * r0 + i.val)).coeff t : ZMod p) *
      (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
      palindromicRatResidue p
        (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) =
    ∑ u ∈ Finset.range 65,
      (X * (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        oddPrimeWeight p).coeff ((u + 1) * p + ell.val) *
          palindromicRatResidue p (momentRat u k) := by
  let P : (ZMod p)[X] := (rowP p (p * r0 + i.val)).map (Int.castRingHom (ZMod p))
  let Q : (ZMod p)[X] := X * P * oddPrimeWeight p
  have hP : ∀ t, 65 * p ≤ t → P.coeff t = 0 := by
    intro t ht
    simp only [P, coeff_map, palindromicZModIntCast_apply,
      rowP_coeff_eq_zero_of_ge hp.out.pos (show H p ≤ t from ht), Int.cast_zero]
  have h := oddPrime_P_coefficient_contraction (B := 65) (k := k)
    hp.out.pos ell.isLt P hP (fun v => palindromicRatResidue p (momentRatSigned v k))
  have hzero : Q.coeff ell.val = 0 :=
    palindromic_actual_P_extraction_below hp2 hr i ell
  have hshift :
      (∑ v ∈ Finset.range (65 + 1), Q.coeff (v * p + ell.val) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k)) =
      ∑ u ∈ Finset.range 65, Q.coeff ((u + 1) * p + ell.val) *
        palindromicRatResidue p (momentRat u k) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      momentRatSigned_natCast, zero_mul, zero_add, hzero, add_zero]
  have hh :
      (∑ t ∈ Finset.range (65 * p), ((rowP p (p * r0 + i.val)).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
        palindromicRatResidue p
          (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) =
      ∑ v ∈ Finset.range (65 + 1), Q.coeff (v * p + ell.val) *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) k) := by
    simpa only [P, Q, coeff_map, palindromicZModIntCast_apply] using h
  exact hh.trans hshift

theorem palindromic_D_digit_contraction {p r0 : ℕ} [hp : Fact p.Prime]
    (i ell : Fin p) (k : ℕ) :
    (∑ t ∈ Finset.range (65 * p), ((rowD p (p * r0 + i.val)).coeff t : ZMod p) *
      (if t % p = ell.val then palindromicRatResidue p (zetaRat (t / p) k) else 0)) =
    ∑ u ∈ Finset.range 65,
      ((rowD p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) *
        palindromicRatResidue p (zetaRat u k) := by
  simpa only [mul_ite, mul_zero] using
    (oddPrime_block_residue_sum_gather (B := 65) hp.out.pos ell.isLt
      (fun t => ((rowD p (p * r0 + i.val)).coeff t : ZMod p))
      (fun u => palindromicRatResidue p (zetaRat u k)))

theorem palindromic_rawEntryRat_prime_digit_reduction {p r0 k : ℕ}
    [hp : Fact p.Prime] (hp260 : 260 < p) (hr : r0 < 48)
    (i ell : Fin p) (hk : k < 65) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * rawEntryRat z p (p * r0 + i.val) (k * p + ell.val)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * rawEntryRat z p (p * r0 + i.val) (k * p + ell.val)) =
      palindromicExtractedRawContraction p r0 i ell k := by
  have hp2 : p ≠ 2 := by omega
  have hH : H p < p ^ 2 := by unfold H; nlinarith
  have hbound : (k + 1) * p ≤ 65 * p := Nat.mul_le_mul_right p hk
  have hj : k * p + ell.val < H p := by
    unfold H
    have hell := ell.isLt
    nlinarith
  have hquot : (k * p + ell.val) / p = k := by
    rw [Nat.mul_comm k p, Nat.mul_add_div hp.out.pos,
      Nat.div_eq_of_lt ell.isLt, add_zero]
  have hmod : (k * p + ell.val) % p = ell.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt ell.isLt]
  have hraw := rawEntryRat_prime_digit_reduction (p := p) (r := p * r0 + i.val)
    hp2 hH hj z hz
  refine ⟨hraw.1, ?_⟩
  have hres :
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * rawEntryRat z p (p * r0 + i.val) (k * p + ell.val)) =
      (∑ t ∈ Finset.range (65 * p), ((rowP p (p * r0 + i.val)).coeff t : ZMod p) *
        (oddPrimeWeight p).coeff (oddPrimeDigitRemainder p t (k * p + ell.val)) *
        palindromicRatResidue p
          (momentRatSigned (oddPrimeDigitRow p t (k * p + ell.val)) k)) -
      (3 / 2 : ZMod p) *
        ∑ t ∈ Finset.range (65 * p), ((rowD p (p * r0 + i.val)).coeff t : ZMod p) *
          (if t % p = ell.val then palindromicRatResidue p (zetaRat (t / p) k) else 0) := by
    simpa only [H, palindromicRatResidue, hquot, hmod] using hraw.2
  rw [hres, palindromic_P_digit_contraction hp2 hr i ell k,
    palindromic_D_digit_contraction i ell k]
  rfl

end InternalCatalan

end



namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrime_central_P_coefficient {p H ell : ℕ} (hp : 0 < p)
    (hH : H ≤ 2 * p) (P : (ZMod p)[X]) (hP : ∀ i, H ≤ i → P.coeff i = 0) :
    (∑ i ∈ Finset.range H, P.coeff i *
      (if p + ell ≤ i then 2 * (oddPrimeWeight p).coeff (2 * p + ell - 1 - i) else 0)) =
      2 * (X * P * oddPrimeWeight p).coeff (2 * p + ell) := by
  rw [oddPrimeExtraction_coeff hp P hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < H := Finset.mem_range.mp hi
  by_cases hactive : p + ell ≤ i
  · have hd : 2 * p + ell - 1 - i < p := by omega
    have hindex : 2 * p + ell = i + 1 + (2 * p + ell - 1 - i) := by omega
    rw [ite_eq_left hactive, Finset.sum_eq_single (2 * p + ell - 1 - i)]
    · rw [ite_eq_left hindex]
      ring
    · intro d hd' hne
      have hneq : 2 * p + ell ≠ i + 1 + d := by omega
      rw [ite_eq_right hneq]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hd)).elim
  · rw [ite_eq_right hactive, mul_zero]
    have hz : (∑ d ∈ Finset.range p,
        if 2 * p + ell = i + 1 + d then P.coeff i * (oddPrimeWeight p).coeff d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hd' : d < p := Finset.mem_range.mp hd
      have hneq : 2 * p + ell ≠ i + 1 + d := by omega
      rw [ite_eq_right hneq]
    rw [hz, mul_zero]

end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rowD_zetaRat_central_reduction_coeff {p N r j : ℕ} [hp : Fact p.Prime]
    (_hN : 0 < N) (hpH : p ≤ H N) (_hH : H N ≤ 2 * p)
    (hJ : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) *
        (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)) =
          -(∑ ell ∈ Finset.range (H N - p),
            ((rowD N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
  let f : ℕ → ℚ := fun i => ((rowD N r).coeff i : ℚ) * ((p : ℚ) * zetaRat i j)
  have hlow (i : ℕ) (hi : i < p) :
      ((f i).den : ZMod p) ≠ 0 ∧ palindromicRatResidue p (f i) = 0 := by
    have hzeta := zetaRat_central_low_reduction hi hj
    have hmul := rational_residue_mul (a := ((rowD N r).coeff i : ℚ))
      (by simp) hzeta.1
    refine ⟨hmul.1, ?_⟩
    change palindromicRatResidue p
      (((rowD N r).coeff i : ℚ) * ((p : ℚ) * zetaRat i j)) = 0
    rw [palindromicRatResidue_mul (by simp) hzeta.1, hzeta.2, mul_zero]
  have hhigh (ell : ℕ) (hell : ell < H N - p) :
      ((f (p + ell)).den : ZMod p) ≠ 0 ∧
        palindromicRatResidue p (f (p + ell)) =
          -(((rowD N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
    have hellj : ell < j := hell.trans_le hJ
    have hzeta := zetaRat_central_high_reduction (p := p) hellj hj
    have hmul := rational_residue_mul (a := ((rowD N r).coeff (p + ell) : ℚ))
      (by simp) hzeta.1
    have hden : (ell : ZMod p) - (j : ZMod p) = -((j - ell : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_lt hellj)]
      ring
    refine ⟨hmul.1, ?_⟩
    change palindromicRatResidue p
      (((rowD N r).coeff (p + ell) : ℚ) * ((p : ℚ) * zetaRat (p + ell) j)) = _
    rw [palindromicRatResidue_mul (by simp) hzeta.1,
      palindromicRatResidue_intCast, hzeta.2, hden, div_neg]
    ring
  have hden (i : ℕ) (hi : i ∈ Finset.range (H N)) : ((f i).den : ZMod p) ≠ 0 := by
    have hiH := Finset.mem_range.mp hi
    by_cases hip : i < p
    · exact (hlow i hip).1
    · have heq : p + (i - p) = i := by omega
      have h := (hhigh (i - p) (by omega)).1
      simpa only [heq] using h
  have hsum := rational_residue_sum (Finset.range (H N)) f hden
  have hscale : (p : ℚ) *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j) =
        ∑ i ∈ Finset.range (H N), f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    ring
  have hsplit :
      (∑ i ∈ Finset.range (H N), palindromicRatResidue p (f i)) =
        (∑ i ∈ Finset.range p, palindromicRatResidue p (f i)) +
        ∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f (p + ell)) := by
    conv_lhs => rw [show H N = p + (H N - p) by omega, Finset.sum_range_add]
  have hlowSum : (∑ i ∈ Finset.range p, palindromicRatResidue p (f i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact (hlow i (Finset.mem_range.mp hi)).2
  have hhighSum :
      (∑ ell ∈ Finset.range (H N - p), palindromicRatResidue p (f (p + ell))) =
        -(∑ ell ∈ Finset.range (H N - p),
          ((rowD N r).coeff (p + ell) : ZMod p) / ((j - ell : ℕ) : ZMod p)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ell hell => (hhigh ell (Finset.mem_range.mp hell)).2)
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hsum.1
  · rw [hscale]
    change (( (∑ i ∈ Finset.range (H N), f i).num : ZMod p) /
      ((∑ i ∈ Finset.range (H N), f i).den : ZMod p)) = _
    rw [hsum.2]
    change (∑ i ∈ Finset.range (H N), palindromicRatResidue p (f i)) = _
    rw [hsplit, hlowSum, zero_add, hhighSum]

theorem rowD_zetaRat_central_reduction {p N r j : ℕ} [hp : Fact p.Prime]
    (hN : 0 < N) (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hjlo : H N - p ≤ j) (hj : j < p) :
    (((p : ℚ) *
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) *
        (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j)) =
          -(∑ ell ∈ Finset.range (H N - p),
            oddPrimeExtractedD p N r ell 1 / ((j - ell : ℕ) : ZMod p)) := by
  simpa only [oddPrimeExtractedD, Nat.one_mul] using
    rowD_zetaRat_central_reduction_coeff (p := p) (N := N) (r := r) (j := j)
      hN hpH hH hjlo hj

end InternalCatalan

end

end OAI
