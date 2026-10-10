import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeCentralZetaContraction

namespace OAI


namespace InternalCatalan

theorem rational_valuation_nonneg_of_den_ne_zero {p : ℕ} [Fact p.Prime]
    {q : ℚ} (hd : (q.den : ZMod p) ≠ 0) : 0 ≤ padicValRat p q := by
  have hnot : ¬p ∣ q.den := fun h =>
    hd ((ZMod.natCast_eq_zero_iff q.den p).mpr h)
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hnot]
  simp only [Nat.cast_zero, sub_zero]
  exact_mod_cast (Nat.zero_le (padicValInt p q.num))

theorem rational_zero_or_valuation_pos_of_residue_zero {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hd : (q.den : ZMod p) ≠ 0)
    (hr : (q.num : ZMod p) / (q.den : ZMod p) = 0) :
    q = 0 ∨ 1 ≤ padicValRat p q := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · apply Or.inr
    have hn : (q.num : ZMod p) = 0 := by
      have h := congrArg (fun x : ZMod p => x * (q.den : ZMod p)) hr
      simpa only [div_mul_cancel₀ _ hd, zero_mul] using h
    have hdiv : (p : ℤ) ∣ q.num :=
      (CharP.intCast_eq_zero_iff (ZMod p) p q.num).mp hn
    have hnval : padicValInt p q.num ≠ 0 := by
      intro hz
      rcases padicValInt.eq_zero_iff.mp hz with hp1 | hnum | hnot
      · exact hp.out.ne_one hp1
      · exact hq (Rat.num_eq_zero.mp hnum)
      · exact hnot hdiv
    have hden : ¬p ∣ q.den := fun h =>
      hd ((ZMod.natCast_eq_zero_iff q.den p).mpr h)
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden]
    simp only [Nat.cast_zero, sub_zero]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnval)

theorem rational_div_prime_den_ne_zero_of_residue_zero {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hd : (q.den : ZMod p) ≠ 0)
    (hr : (q.num : ZMod p) / (q.den : ZMod p) = 0) :
    ((q / (p : ℚ)).den : ZMod p) ≠ 0 := by
  rcases rational_zero_or_valuation_pos_of_residue_zero hd hr with hq | hv
  · simp [hq]
  · have hq : q ≠ 0 := by
      intro hz
      rw [hz, padicValRat.zero] at hv
      omega
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    apply rational_den_ne_zero_of_valuation_nonneg
    rw [padicValRat.div hq hpq, padicValRat.self hp.out.one_lt]
    omega

theorem rational_den_ne_zero_of_prime_mul_residue_zero {p : ℕ} [hp : Fact p.Prime]
    {q : ℚ} (hd : (((p : ℚ) * q).den : ZMod p) ≠ 0)
    (hr : (((p : ℚ) * q).num : ZMod p) /
      (((p : ℚ) * q).den : ZMod p) = 0) : (q.den : ZMod p) ≠ 0 := by
  have h := rational_div_prime_den_ne_zero_of_residue_zero hd hr
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have heq : (p : ℚ) * q / p = q := by field_simp [hpq]
  rwa [heq] at h

theorem rational_prime_scaled_den_ne_zero_of_prime_sq_residue_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hd : (((p : ℚ) ^ 2 * q).den : ZMod p) ≠ 0)
    (hr : (((p : ℚ) ^ 2 * q).num : ZMod p) /
      (((p : ℚ) ^ 2 * q).den : ZMod p) = 0) :
    (((p : ℚ) * q).den : ZMod p) ≠ 0 := by
  have heq : (p : ℚ) * ((p : ℚ) * q) = (p : ℚ) ^ 2 * q := by ring
  apply rational_den_ne_zero_of_prime_mul_residue_zero
  · rw [heq]
    exact hd
  · rw [heq]
    exact hr





theorem zmod_val_rat_reduction {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    (((x.val : ℚ).den : ZMod p) ≠ 0) ∧
      palindromicRatResidue p (x.val : ℚ) = x := by
  constructor
  · rw [Rat.den_natCast, Nat.cast_one]
    exact one_ne_zero
  · simp only [palindromicRatResidue, Rat.num_natCast, Rat.den_natCast,
      Nat.cast_one, div_one, Int.cast_natCast]
    simp

theorem rational_remainder_den_ne_zero_of_scaled_residue_eq
    {p : ℕ} [hp : Fact p.Prime] {q s : ℚ}
    (hq : (((p : ℚ) * q).den : ZMod p) ≠ 0)
    (hs : (s.den : ZMod p) ≠ 0)
    (he : palindromicRatResidue p ((p : ℚ) * q) = palindromicRatResidue p s) :
    ((q - s / (p : ℚ)).den : ZMod p) ≠ 0 := by
  have hsub := rational_residue_sub hq hs
  have hzero : (((p : ℚ) * q - s).num : ZMod p) /
      (((p : ℚ) * q - s).den : ZMod p) = 0 := by
    change palindromicRatResidue p ((p : ℚ) * q - s) = 0
    rw [palindromicRatResidue_sub hq hs, he, sub_self]
  have hdiv := rational_div_prime_den_ne_zero_of_residue_zero hsub.1 hzero
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have halgebra : ((p : ℚ) * q - s) / p = q - s / p := by
    field_simp [hpq]
  rwa [halgebra] at hdiv

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem oddPrimeExtractedP_eq_zero_of_ge_three {p N r ell v : ℕ}
    (hp : 0 < p) (hN : 0 < N) (hwidth : H N ≤ ell + 2 * p) (hv : 3 ≤ v) :
    oddPrimeExtractedP p N r ell v = 0 := by
  have hP : ∀ i, H N ≤ i →
      ((rowP N r).map (Int.castRingHom (ZMod p))).coeff i = 0 := by
    intro i hi
    simp only [coeff_map, rowP_coeff_eq_zero_of_ge hN hi, map_zero]
  unfold oddPrimeExtractedP
  rw [oddPrimeExtraction_coeff hp _ hP]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro d hd
  have hi' := Finset.mem_range.mp hi
  have hd' := Finset.mem_range.mp hd
  have hmul := Nat.mul_le_mul_right p hv
  have hneq : v * p + ell ≠ i + 1 + d := by omega
  simp only [ite_eq_right hneq]

theorem oddPrimeExtractedD_eq_zero_of_ge_two {p N r ell u : ℕ}
    (hN : 0 < N) (hwidth : H N ≤ ell + 2 * p) (hu : 2 ≤ u) :
    oddPrimeExtractedD p N r ell u = 0 := by
  have hmul := Nat.mul_le_mul_right p hu
  have hindex : H N ≤ u * p + ell := by omega
  unfold oddPrimeExtractedD
  rw [rowD_coeff_eq_zero_of_ge hN hindex, Int.cast_zero]

theorem oddPrimeExtractedP_zero_of_le_A {p N r ell : ℕ}
    (hp : 0 < p) (hN : 0 < N) (hr : r < n N) (hell : ell ≤ A N) :
    oddPrimeExtractedP p N r ell 0 = 0 := by
  have hP : ∀ i, H N ≤ i →
      ((rowP N r).map (Int.castRingHom (ZMod p))).coeff i = 0 := by
    intro i hi
    simp only [coeff_map, rowP_coeff_eq_zero_of_ge hN hi, map_zero]
  unfold oddPrimeExtractedP
  simp only [Nat.zero_mul, zero_add]
  rw [oddPrimeExtraction_coeff hp _ hP]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro d hd
  by_cases heq : ell = i + 1 + d
  · have hicoeff : (rowP N r).coeff i = 0 :=
      rowP_coeff_eq_zero_of_lt hN hr (by omega)
    simp only [ite_eq_left heq, coeff_map, hicoeff, map_zero, zero_mul]
  · simp only [ite_eq_right heq]

theorem oddPrimeExtractedD_zero_of_le_A {p N r ell : ℕ}
    (hN : 0 < N) (hr : r < n N) (hell : ell ≤ A N) :
    oddPrimeExtractedD p N r ell 0 = 0 := by
  unfold oddPrimeExtractedD
  simp only [Nat.zero_mul, zero_add,
    rowD_coeff_eq_zero_of_lt hN hr (show ell < A N + 1 by omega), Int.cast_zero]

def oddPrimeLeadingU (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2 * oddPrimeExtractedP p N r ell 0 - (3 / 2 : ZMod p) * oddPrimeExtractedD p N r ell 0

theorem oddPrimeLeadingU_eq_zero {p N r ell : ℕ} [Fact p.Prime]
    (hp : 0 < p) (hN : 0 < N) (hr : r < n N) (hell : ell ≤ A N) :
    oddPrimeLeadingU p N r ell = 0 := by
  unfold oddPrimeLeadingU
  rw [oddPrimeExtractedP_zero_of_le_A hp hN hr hell,
    oddPrimeExtractedD_zero_of_le_A hN hr hell]
  ring

private theorem paired_moment_values {p : ℕ} [Fact p.Prime] (v : ℕ) (hv : v < 3) :
    palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0) +
      palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1) =
        if v = 0 then 2 else 0 := by
  have hcases : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    norm_num [palindromicRatResidue, momentRatSigned, momentRatNegOne,
      momentRat, boundaryPlus, boundaryMinus, momentScalar, centralCoeff,
      Finset.sum_range_succ]

private theorem paired_zeta_values {p : ℕ} [Fact p.Prime] (u : ℕ) (hu : u < 2) :
    palindromicRatResidue p (zetaRat u 0) + palindromicRatResidue p (zetaRat u 1) =
      if u = 0 then 1 else 0 := by
  have hcases : u = 0 ∨ u = 1 := by omega
  rcases hcases with rfl | rfl <;>
    norm_num [palindromicRatResidue, zetaRat, harmonicRat, Finset.sum_range_succ]

theorem rawEntryRat_pair_leading {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))) =
          oddPrimeLeadingU p N r ell := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hH : H N < p ^ 2 := by nlinarith
  have hH2 : 2 ≤ H N := by unfold H; omega
  have hlo := rawEntryRat_general_column_layer (k := 0) (N := N) (r := r)
    hp2 hN hH hell (by simpa using (show ell < H N by omega)) z hz
  have hhi := rawEntryRat_general_column_layer (k := 1) (N := N) (r := r)
    hp2 hN hH hell (by simpa using hhigh) z hz
  simp only [Nat.zero_mul, zero_add] at hlo
  simp only [Nat.one_mul] at hhi
  have hMsum :
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) +
      (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
        palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1)) =
          2 * oddPrimeExtractedP p N r ell 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ v ∈ Finset.range 3,
          (oddPrimeExtractedP p N r ell v *
            palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0) +
           oddPrimeExtractedP p N r ell v *
            palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1)) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (show 3 ≤ H N + 1 by omega))
        intro v hv hnot
        have hv3 : 3 ≤ v := by simpa only [Finset.mem_range, not_lt] using hnot
        rw [oddPrimeExtractedP_eq_zero_of_ge_three hp.out.pos hN hwidth hv3]
        ring
      _ = ∑ v ∈ Finset.range 3,
          oddPrimeExtractedP p N r ell v * (if v = 0 then 2 else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← mul_add, paired_moment_values v (Finset.mem_range.mp hv)]
      _ = _ := by
        norm_num [Finset.sum_range_succ]
        ring
  have hZsum :
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 0)) +
      (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
        palindromicRatResidue p (zetaRat u 1)) = oddPrimeExtractedD p N r ell 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ u ∈ Finset.range 2,
          (oddPrimeExtractedD p N r ell u * palindromicRatResidue p (zetaRat u 0) +
           oddPrimeExtractedD p N r ell u * palindromicRatResidue p (zetaRat u 1)) := by
        symm
        apply Finset.sum_subset (Finset.range_mono hH2)
        intro u hu hnot
        have hu2 : 2 ≤ u := by simpa only [Finset.mem_range, not_lt] using hnot
        rw [oddPrimeExtractedD_eq_zero_of_ge_two hN hwidth hu2]
        ring
      _ = ∑ u ∈ Finset.range 2,
          oddPrimeExtractedD p N r ell u * (if u = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [← mul_add, paired_zeta_values u (Finset.mem_range.mp hu)]
      _ = _ := by simp
  have hres :
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r ell) +
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat z N r (p + ell)) =
          oddPrimeLeadingU p N r ell := by
    rw [hlo.2, hhi.2]
    calc
      _ =
        ((∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
          palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 0)) +
         (∑ v ∈ Finset.range (H N + 1), oddPrimeExtractedP p N r ell v *
          palindromicRatResidue p (momentRatSigned ((v : ℤ) - 1) 1))) -
        (3 / 2 : ZMod p) *
        ((∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
          palindromicRatResidue p (zetaRat u 0)) +
         (∑ u ∈ Finset.range (H N), oddPrimeExtractedD p N r ell u *
          palindromicRatResidue p (zetaRat u 1))) := by ring
      _ = _ := by rw [hMsum, hZsum]; rfl
  have hadd := rational_residue_add hlo.1 hhi.1
  refine ⟨?_, ?_⟩
  · rw [mul_add]
    exact hadd.1
  · rw [mul_add, palindromicRatResidue_add hlo.1 hhi.1]
    exact hres

theorem rawEntryRat_pair_scaled_reduction {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hell : ell < p)
    (hwidth : H N ≤ ell + 2 * p) (hhigh : p + ell < H N) (hellA : ell ≤ A N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))).den :
        ZMod p) ≠ 0 ∧
      palindromicRatResidue p
        ((p : ℚ) ^ 2 * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))) = 0 := by
  have hpair := rawEntryRat_pair_leading (r := r) hp2 hN hell hwidth hhigh z hz
  exact ⟨hpair.1, hpair.2.trans (oddPrimeLeadingU_eq_zero hp.out.pos hN hr hellA)⟩

end InternalCatalan

end



namespace InternalCatalan

theorem rawEntryRat_pair_prime_scaled_den_ne_zero {p N r ell : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hell : ell < p)
    (hH : H N ≤ ell + 2 * p) (hhigh : p + ell < H N) (hA : ell ≤ A N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (((p : ℚ) * (rawEntryRat z N r ell + rawEntryRat z N r (p + ell))).den :
      ZMod p) ≠ 0 := by
  have hpair := rawEntryRat_pair_scaled_reduction hp2 hN hr hell hH hhigh hA z hz
  apply rational_prime_scaled_den_ne_zero_of_prime_sq_residue_zero hpair.1
  simpa only [palindromicRatResidue] using hpair.2

theorem rawEntryRat_pair_valuation_lower {p N r ell : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hr : r < n N) (hell : ell < p)
    (hH : H N ≤ ell + 2 * p) (hhigh : p + ell < H N) (hA : ell ≤ A N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -1 ≤ padicValRat p (rawEntryRat z N r ell + rawEntryRat z N r (p + ell)) := by
  have hd := rawEntryRat_pair_prime_scaled_den_ne_zero hp2 hN hr hell hH hhigh hA z hz
  have hv := rational_valuation_nonneg_of_den_ne_zero hd
  by_cases hzero : rawEntryRat z N r ell + rawEntryRat z N r (p + ell) = 0
  · simp [hzero]
  · have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [padicValRat.mul hpq hzero, padicValRat.self hp.out.one_lt] at hv
    omega

end InternalCatalan

end OAI
