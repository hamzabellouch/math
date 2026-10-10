import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Filter.AtTopBot.Basic
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeCentralZetaContraction
import OAI.NumberTheory.Catalan.Determinants.PalindromicExtractedMatrix
import OAI.NumberTheory.Catalan.Determinants.PalindromicResidueDeterminant
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedDeterminantsNonzero
import OAI.NumberTheory.Catalan.Polynomial.Rationality

namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem oddPrime_multiple_sum_gather {R : Type*} [Semiring R] {p B : ℕ}
    (hp : 0 < p) (f : ℕ → R) :
    (∑ v ∈ Finset.range (B * p + 1), if v % p = 0 then f v else 0) =
      ∑ u ∈ Finset.range (B + 1), f (u * p) := by
  classical
  refine Finset.sum_bij_ne_zero (fun v _ _ => v / p) ?_ ?_ ?_ ?_
  · intro v hv hfv
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    have hv' := Finset.mem_range.mp hv
    nlinarith
  · intro v hv hfv w hw hfw hquot
    have hvr : v % p = 0 := by
      by_contra h
      exact hfv (ite_eq_right h)
    have hwr : w % p = 0 := by
      by_contra h
      exact hfw (ite_eq_right h)
    have hdv := Nat.mod_add_div v p
    have hdw := Nat.mod_add_div w p
    rw [hvr, hquot, zero_add] at hdv
    rw [hwr, zero_add] at hdw
    omega
  · intro u hu hfu
    have hu' : u ≤ B := by have := Finset.mem_range.mp hu; omega
    have hbound := Nat.mul_le_mul_right p hu'
    refine ⟨u * p, Finset.mem_range.mpr (by omega), ?_, Nat.mul_div_cancel u hp⟩
    simpa only [Nat.mul_mod_left, ite_eq_left rfl, ite_true] using hfu
  · intro v hv hfv
    have hvr : v % p = 0 := by
      by_contra h
      exact hfv (ite_eq_right h)
    have heq : v / p * p = v := by
      have h := Nat.mod_add_div v p
      rw [hvr, zero_add] at h
      simpa only [Nat.mul_comm] using h
    rw [ite_eq_left hvr, heq]

theorem palindromic_filteredEntryRat_prime_digit_reduction {p : ℕ}
    [hp : Fact p.Prime] (hp260 : 260 < p) (r0 : Fin 48) (i ell : Fin p)
    (k0 : Fin 48) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * filteredEntryRat z p (p * r0.val + i.val)
      (ell.val + p * k0.val)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat z p
        (p * r0.val + i.val) (ell.val + p * k0.val)) =
      palindromicExtractedFilteredEntry p r0 i ell k0 := by
  have hcol : ell.val + p * k0.val < n p := by
    unfold n
    have hb := Nat.mul_le_mul_left p k0.isLt
    have hell := ell.isLt
    nlinarith
  have hs := filteredEntryRat_prime_scaled_residue_sum (r := p * r0.val + i.val)
    hp260 hcol z hz
  refine ⟨hs.1, ?_⟩
  let f : ℕ → ZMod p := fun v =>
    palindromicBaseFilterWeight p (v / p) *
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z p
        (p * r0.val + i.val) (b p + (ell.val + p * k0.val) + v))
  have hsum :
      palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat z p
        (p * r0.val + i.val) (ell.val + p * k0.val)) =
      ∑ v ∈ Finset.range (4 * p + 1), if v % p = 0 then f v else 0 := by
    calc
      _ = ∑ v ∈ Finset.range (q p + 1), palindromicRatResidue p (filterCoeffRat p v) *
          palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z p
            (p * r0.val + i.val) (b p + (ell.val + p * k0.val) + v)) := hs.2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have hd := (filterCoeffRat_prime_digit_reduction (p := p) (v := v)).2
        change palindromicRatResidue p (filterCoeffRat p v) = _ at hd
        rw [hd]
        split_ifs <;> simp only [f, palindromicBaseFilterWeight, zero_mul]
  rw [hsum, oddPrime_multiple_sum_gather hp.out.pos]
  unfold palindromicExtractedFilteredEntry
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u < 5 := Finset.mem_range.mp hu
  have hk : 7 + k0.val + u < 65 := by have := k0.isLt; omega
  have hindex : b p + (ell.val + p * k0.val) + u * p =
      (7 + k0.val + u) * p + ell.val := by unfold b; ring
  dsimp only [f]
  rw [Nat.mul_div_cancel u hp.out.pos, hindex,
    (palindromic_rawEntryRat_prime_digit_reduction hp260 r0.isLt i ell hk z hz).2]

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem palindromicScaledRatMatrix_entry_den_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (r k : Fin p × Fin 48) :
    ((palindromicScaledRatMatrix z p r k).den : ZMod p) ≠ 0 :=
  (palindromic_filteredEntryRat_prime_digit_reduction hp r.2 r.1 k.1 k.2 z hz).1

theorem palindromicScaledResidueMatrix_eq_extracted {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    palindromicScaledResidueMatrix z p = palindromicExtractedResidueMatrix p := by
  ext r k
  exact (palindromic_filteredEntryRat_prime_digit_reduction hp r.2 r.1 k.1 k.2 z hz).2

theorem palindromicScaledResidueMatrix_eq_blocks {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    palindromicScaledResidueMatrix z p = palindromicResidueBlockMatrix p := by
  rw [palindromicScaledResidueMatrix_eq_extracted hp z hz,
    palindromicExtractedResidueMatrix_eq_blocks hp]

def palindromicPrimeCutoff (z : ℚ) : ℕ := max fixedDeterminantPrimeCutoff z.den

theorem determinantRat_prime_ne_zero_of_fixed
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (z : ℚ) {p : ℕ} [Fact p.Prime] (hp : palindromicPrimeCutoff z < p) :
    determinantRat z p ≠ 0 := by
  have hfixed : fixedDeterminantPrimeCutoff < p :=
    lt_of_le_of_lt (le_max_left _ _) hp
  have hp260 : 260 < p :=
    lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hfixed
  have hzbound : z.den < p := lt_of_le_of_lt (le_max_right _ _) hp
  have hz : (z.den : ZMod p) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt z.den_pos hzbound)
      ((ZMod.natCast_eq_zero_iff z.den p).mp hzero)
  have hdet := fixedDeterminants_mod_prime_ne_zero_of_lt hzero hplus hminus hfixed
  apply determinantRat_ne_zero_of_scaledResidueMatrix z
    (palindromicScaledRatMatrix_entry_den_ne_zero hp260 z hz)
  rw [palindromicScaledResidueMatrix_eq_extracted hp260 z hz]
  exact det_palindromicExtractedResidueMatrix_ne_zero_of_fixed
    hp260 hdet.1 hdet.2.1 hdet.2.2

theorem determinantRat_prime_eventually_ne_zero_of_fixed
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0) (z : ℚ) :
    ∃ C : ℕ, ∀ p : ℕ, p.Prime → C < p → determinantRat z p ≠ 0 := by
  refine ⟨palindromicPrimeCutoff z, ?_⟩
  intro p hpPrime hp
  let : Fact p.Prime := ⟨hpPrime⟩
  exact determinantRat_prime_ne_zero_of_fixed hzero hplus hminus z hp

theorem determinant_prime_eventually_ne_zero_of_fixed
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    {z : ℚ} (hz : (z : ℝ) = catalan) :
    ∃ C : ℕ, ∀ p : ℕ, p.Prime → C < p → determinant p ≠ 0 := by
  obtain ⟨C, hC⟩ := determinantRat_prime_eventually_ne_zero_of_fixed
    hzero hplus hminus z
  refine ⟨C, ?_⟩
  intro p hpPrime hp
  exact (determinantRat_ne_zero_iff hz hpPrime.pos).mp (hC p hpPrime hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem padicValRat_eq_zero_of_palindromicRatResidue_ne_zero
    {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hden : (x.den : ZMod p) ≠ 0)
    (hres : palindromicRatResidue p x ≠ 0) : padicValRat p x = 0 := by
  have hnum : (x.num : ZMod p) ≠ 0 := by
    intro hzero
    apply hres
    simp only [palindromicRatResidue, hzero, zero_div]
  have hn : ¬ (p : ℤ) ∣ x.num := by
    intro hdiv
    exact hnum ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mpr hdiv)
  have hd : ¬ p ∣ x.den := by
    intro hdiv
    exact hden ((ZMod.natCast_eq_zero_iff x.den p).mpr hdiv)
  simp only [padicValRat, padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero, sub_zero]

theorem palindromicScaledRatMatrix_det_valuation_zero
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (z : ℚ) {p : ℕ} [Fact p.Prime] (hp : palindromicPrimeCutoff z < p) :
    padicValRat p (palindromicScaledRatMatrix z p).det = 0 := by
  have hfixed : fixedDeterminantPrimeCutoff < p :=
    lt_of_le_of_lt (le_max_left _ _) hp
  have hp260 : 260 < p :=
    lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hfixed
  have hzbound : z.den < p := lt_of_le_of_lt (le_max_right _ _) hp
  have hz : (z.den : ZMod p) ≠ 0 := by
    intro hden
    exact (Nat.not_dvd_of_pos_of_lt z.den_pos hzbound)
      ((ZMod.natCast_eq_zero_iff z.den p).mp hden)
  have hfixedres := fixedDeterminants_mod_prime_ne_zero_of_lt
    hzero hplus hminus hfixed
  have hdet : (palindromicScaledResidueMatrix z p).det ≠ 0 := by
    rw [palindromicScaledResidueMatrix_eq_extracted hp260 z hz]
    exact det_palindromicExtractedResidueMatrix_ne_zero_of_fixed
      hp260 hfixedres.1 hfixedres.2.1 hfixedres.2.2
  have hres := palindromicScaledRatMatrix_det_residue z
    (palindromicScaledRatMatrix_entry_den_ne_zero hp260 z hz)
  apply padicValRat_eq_zero_of_palindromicRatResidue_ne_zero hres.1
  rw [hres.2]
  exact hdet

theorem determinantRat_prime_valuation_of_fixed
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (z : ℚ) {p : ℕ} [hpPrime : Fact p.Prime]
    (hp : palindromicPrimeCutoff z < p) :
    padicValRat p (determinantRat z p) = -96 * (p : ℤ) := by
  have hval := palindromicScaledRatMatrix_det_valuation_zero hzero hplus hminus z hp
  have hdet := determinantRat_prime_ne_zero_of_fixed hzero hplus hminus z hp
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
  rw [det_palindromicScaledRatMatrix,
    padicValRat.mul (pow_ne_zero _ hpq) hdet, padicValRat.pow,
    padicValRat.self hpPrime.out.one_lt, mul_one] at hval
  simp only [n, Nat.cast_mul, Nat.cast_ofNat] at hval
  omega

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem determinantRat_prime_ne_zero (z : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : palindromicPrimeCutoff z < p) : determinantRat z p ≠ 0 :=
  determinantRat_prime_ne_zero_of_fixed fixedMatrix_zero_det_ne_zero
    fixedMatrix_one_det_ne_zero fixedMatrix_neg_one_det_ne_zero z hp

theorem determinantRat_prime_valuation (z : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : palindromicPrimeCutoff z < p) :
    padicValRat p (determinantRat z p) = -96 * (p : ℤ) :=
  determinantRat_prime_valuation_of_fixed fixedMatrix_zero_det_ne_zero
    fixedMatrix_one_det_ne_zero fixedMatrix_neg_one_det_ne_zero z hp

theorem determinant_prime_eventually_ne_zero {z : ℚ} (hz : (z : ℝ) = catalan) :
    ∃ C : ℕ, ∀ p : ℕ, p.Prime → C < p → determinant p ≠ 0 :=
  determinant_prime_eventually_ne_zero_of_fixed fixedMatrix_zero_det_ne_zero
    fixedMatrix_one_det_ne_zero fixedMatrix_neg_one_det_ne_zero hz

def nonzeroPrimeScale (z : ℚ) (k : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (palindromicPrimeCutoff z + k + 1))

theorem nonzeroPrimeScale_bound (z : ℚ) (k : ℕ) :
    palindromicPrimeCutoff z + k + 1 ≤ nonzeroPrimeScale z k :=
  (Classical.choose_spec
    (Nat.exists_infinite_primes (palindromicPrimeCutoff z + k + 1))).1

theorem nonzeroPrimeScale_prime (z : ℚ) (k : ℕ) : (nonzeroPrimeScale z k).Prime :=
  (Classical.choose_spec
    (Nat.exists_infinite_primes (palindromicPrimeCutoff z + k + 1))).2

theorem nonzeroPrimeScale_tendsto (z : ℚ) :
    Filter.Tendsto (nonzeroPrimeScale z) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, ?_⟩
  intro k hk
  have hbound := nonzeroPrimeScale_bound z k
  omega

theorem determinantRat_nonzeroPrimeScale_ne_zero (z : ℚ) (k : ℕ) :
    determinantRat z (nonzeroPrimeScale z k) ≠ 0 := by
  let : Fact (nonzeroPrimeScale z k).Prime := ⟨nonzeroPrimeScale_prime z k⟩
  apply determinantRat_prime_ne_zero
  have hbound := nonzeroPrimeScale_bound z k
  omega

theorem determinant_nonzeroPrimeScale_ne_zero {z : ℚ}
    (hz : (z : ℝ) = catalan) (k : ℕ) : determinant (nonzeroPrimeScale z k) ≠ 0 :=
  (determinantRat_ne_zero_iff hz (nonzeroPrimeScale_prime z k).pos).mp
    (determinantRat_nonzeroPrimeScale_ne_zero z k)

theorem exists_nonzero_prime_scales {z : ℚ} (hz : (z : ℝ) = catalan) :
    ∃ s : ℕ → ℕ, Filter.Tendsto s Filter.atTop Filter.atTop ∧
      ∀ k, (s k).Prime ∧ determinant (s k) ≠ 0 := by
  exact ⟨nonzeroPrimeScale z, nonzeroPrimeScale_tendsto z,
    fun k => ⟨nonzeroPrimeScale_prime z k, determinant_nonzeroPrimeScale_ne_zero hz k⟩⟩

end InternalCatalan

end

end

end OAI
