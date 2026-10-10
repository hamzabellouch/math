import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI


namespace InternalCatalan

def oddPrimeDigitRemainder (p i j : ℕ) : ℕ :=
  (((j : ℤ) - (i : ℤ) - 1) % (p : ℤ)).toNat

def oddPrimeDigitRow (p i j : ℕ) : ℤ :=
  ((i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ)) /
    (p : ℤ) - 1

theorem oddPrimeDigitRemainder_lt {p i j : ℕ} (hp : 0 < p) :
    oddPrimeDigitRemainder p i j < p := by
  unfold oddPrimeDigitRemainder
  have hpz : 0 < (p : ℤ) := by omega
  have hlo := Int.emod_nonneg ((j : ℤ) - (i : ℤ) - 1) (by omega : (p : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos ((j : ℤ) - (i : ℤ) - 1) hpz
  omega

theorem oddPrimeDigitRemainder_of_le {p i j : ℕ} (hp : 0 < p) (hji : j ≤ i) :
    oddPrimeDigitRemainder p i j = p - 1 - (i - j) % p := by
  have hx : (j : ℤ) - (i : ℤ) - 1 = Int.negSucc (i - j) := by omega
  have hr : (i - j) % p < p := Nat.mod_lt _ hp
  unfold oddPrimeDigitRemainder
  rw [hx, Int.negSucc_emod (i - j) (by omega : 0 < (p : ℤ)),
    ← Int.natCast_emod]
  omega

theorem oddPrimeDigitRemainder_of_lt {p i j : ℕ} (_hp : 0 < p) (hij : i < j) :
    oddPrimeDigitRemainder p i j = (j - i - 1) % p := by
  have hx : (j : ℤ) - (i : ℤ) - 1 = ((j - i - 1 : ℕ) : ℤ) := by omega
  unfold oddPrimeDigitRemainder
  rw [hx, ← Int.natCast_emod, Int.toNat_natCast]

private theorem digit_numerator_of_le {p i j : ℕ} (hp : 0 < p) (hji : j ≤ i) :
    (i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ) =
      (p : ℤ) * ((((i - j) / p : ℕ) : ℤ) + ((j / p : ℕ) : ℤ) + 1) := by
  have hr : (i - j) % p < p := Nat.mod_lt _ hp
  have hrem : ((p - 1 - (i - j) % p : ℕ) : ℤ) =
      (p : ℤ) - 1 - (((i - j) % p : ℕ) : ℤ) := by omega
  have hk : (((i - j) % p : ℕ) : ℤ) + (p : ℤ) * (((i - j) / p : ℕ) : ℤ) =
      ((i - j : ℕ) : ℤ) := by exact_mod_cast Nat.mod_add_div (i - j) p
  have hj : ((j % p : ℕ) : ℤ) + (p : ℤ) * ((j / p : ℕ) : ℤ) = (j : ℤ) := by
    exact_mod_cast Nat.mod_add_div j p
  have hsub : ((i - j : ℕ) : ℤ) = (i : ℤ) - (j : ℤ) := by omega
  rw [oddPrimeDigitRemainder_of_le hp hji, hrem]
  nlinarith

private theorem digit_numerator_of_lt {p i j : ℕ} (hp : 0 < p) (hij : i < j) :
    (i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ) =
      (p : ℤ) * (((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ)) := by
  have hk : (((j - i - 1) % p : ℕ) : ℤ) +
      (p : ℤ) * (((j - i - 1) / p : ℕ) : ℤ) = ((j - i - 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.mod_add_div (j - i - 1) p
  have hj : ((j % p : ℕ) : ℤ) + (p : ℤ) * ((j / p : ℕ) : ℤ) = (j : ℤ) := by
    exact_mod_cast Nat.mod_add_div j p
  have hsub : ((j - i - 1 : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) - 1 := by omega
  rw [oddPrimeDigitRemainder_of_lt hp hij]
  nlinarith

theorem oddPrimeDigitRow_numerator_dvd {p i j : ℕ} (hp : 0 < p) :
    (p : ℤ) ∣ (i : ℤ) + 1 + (oddPrimeDigitRemainder p i j : ℤ) - ((j % p : ℕ) : ℤ) := by
  by_cases hji : j ≤ i
  · exact ⟨_, digit_numerator_of_le hp hji⟩
  · exact ⟨_, digit_numerator_of_lt hp (by omega)⟩

theorem oddPrimeDigitRow_of_le {p i j : ℕ} (hp : 0 < p) (hji : j ≤ i) :
    oddPrimeDigitRow p i j = (((i - j) / p : ℕ) : ℤ) + ((j / p : ℕ) : ℤ) := by
  unfold oddPrimeDigitRow
  rw [digit_numerator_of_le hp hji,
    Int.mul_ediv_cancel_left _ (by omega : (p : ℤ) ≠ 0)]
  omega

theorem oddPrimeDigitRow_of_lt {p i j : ℕ} (hp : 0 < p) (hij : i < j) :
    oddPrimeDigitRow p i j = ((j / p : ℕ) : ℤ) - (((j - i - 1) / p : ℕ) : ℤ) - 1 := by
  unfold oddPrimeDigitRow
  rw [digit_numerator_of_lt hp hij,
    Int.mul_ediv_cancel_left _ (by omega : (p : ℤ) ≠ 0)]

theorem oddPrimeDigitRow_lower_bound {p i j : ℕ} (hp : 0 < p) :
    -1 ≤ oddPrimeDigitRow p i j := by
  by_cases hji : j ≤ i
  · rw [oddPrimeDigitRow_of_le hp hji]
    exact (by norm_num : (-1 : ℤ) ≤ 0).trans
      (add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  · rw [oddPrimeDigitRow_of_lt hp (by omega : i < j)]
    have hquot : (j - i - 1) / p ≤ j / p :=
      Nat.div_le_div_right (by omega : j - i - 1 ≤ j)
    omega





theorem oddPrimeExtractionIndices_unique {p i k ell d v : ℕ}
    (hp : 0 < p) (hell : ell < p) (hd : d < p)
    (hindex : i + 1 + d = v * p + ell) :
    d = oddPrimeDigitRemainder p i (k * p + ell) ∧
      oddPrimeDigitRow p i (k * p + ell) = (v : ℤ) - 1 := by
  have hcast : (i : ℤ) + 1 + (d : ℤ) = (v : ℤ) * (p : ℤ) + (ell : ℤ) := by
    exact_mod_cast hindex
  have hdiff : ((k * p + ell : ℕ) : ℤ) - (i : ℤ) - 1 =
      (d : ℤ) + ((k : ℤ) - (v : ℤ)) * (p : ℤ) := by
    push_cast
    nlinarith [hcast]
  have hrem : oddPrimeDigitRemainder p i (k * p + ell) = d := by
    unfold oddPrimeDigitRemainder
    rw [hdiff, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (Int.natCast_nonneg d) (by exact_mod_cast hd),
      Int.toNat_natCast]
  have hcol : (k * p + ell) % p = ell := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hell]
  refine ⟨hrem.symm, ?_⟩
  unfold oddPrimeDigitRow
  rw [hrem, hcol]
  have hnum : (i : ℤ) + 1 + (d : ℤ) - (ell : ℤ) = (p : ℤ) * (v : ℤ) := by
    nlinarith [hcast]
  rw [hnum, Int.mul_ediv_cancel_left _ (by omega : (p : ℤ) ≠ 0)]

theorem oddPrimeExtractionIndices_exists {p H i k ell : ℕ}
    (hp : 0 < p) (hell : ell < p) (hi : i < H) :
    ∃ v ∈ Finset.range (H + 1),
      i + 1 + oddPrimeDigitRemainder p i (k * p + ell) = v * p + ell ∧
        oddPrimeDigitRow p i (k * p + ell) = (v : ℤ) - 1 := by
  by_cases hle : ell ≤ i
  · let v : ℕ := (i - ell) / p + 1
    let d : ℕ := p - 1 - (i - ell) % p
    have hr : (i - ell) % p < p := Nat.mod_lt _ hp
    have hd : d < p := by dsimp only [d]; omega
    have hquot := Nat.mod_add_div (i - ell) p
    have hsub : i - ell + ell = i := Nat.sub_add_cancel hle
    have hdigit : (i - ell) % p + d + 1 = p := by dsimp only [d]; omega
    have hindex : i + 1 + d = v * p + ell := by
      dsimp only [v]
      nlinarith [hquot, hsub, hdigit]
    have hv : v < H + 1 := by
      have hdiv : (i - ell) / p ≤ i - ell := Nat.div_le_self (i - ell) p
      dsimp only [v]
      omega
    have hunique := oddPrimeExtractionIndices_unique (k := k) hp hell hd hindex
    refine ⟨v, Finset.mem_range.mpr hv, ?_, hunique.2⟩
    rw [← hunique.1]
    exact hindex
  · let d : ℕ := ell - i - 1
    have hd : d < p := by dsimp only [d]; omega
    have hindex : i + 1 + d = 0 * p + ell := by dsimp only [d]; omega
    have hunique := oddPrimeExtractionIndices_unique (k := k) hp hell hd hindex
    refine ⟨0, by simp, ?_, hunique.2⟩
    rw [← hunique.1]
    exact hindex

end InternalCatalan

end OAI
