import OAI.NumberTheory.Catalan.Estimates.OddLowerPairPool
import OAI.NumberTheory.Catalan.Estimates.OddPhysicalCombination

namespace OAI


noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

abbrev oddLowerRetainedSize (N p : ℕ) := Fintype.card ↥(oddLowerRetainedSet N p)
abbrev oddLowerPairedSize (N p : ℕ) := Fintype.card ↥(oddLowerPairSet N p)
abbrev oddLowerPhysicalIndex (N p : ℕ) :=
  oddPhysicalIndex (oddLowerRetainedSize N p) (oddLowerPairedSize N p) 0

def oddLowerRetainedTag {N p : ℕ} (j : ↥(oddLowerRetainedSet N p)) :
    oddLowerPhysicalIndex N p := Sum.inl ((Fintype.equivFin _) j)

def oddLowerPairedTag {N p : ℕ} (ell : ↥(oddLowerPairSet N p)) :
    oddLowerPhysicalIndex N p := Sum.inr (Sum.inl ((Fintype.equivFin _) ell))

def oddLowerRetainedVector (z : ℚ) (N p : ℕ)
    (j : Fin (oddLowerRetainedSize N p)) (r : Fin (n N)) : ℚ :=
  (p : ℚ) ^ 2 * rawEntryRat z N r.val
    (((Fintype.equivFin ↥(oddLowerRetainedSet N p)).symm j).val)

def oddLowerPairedVector (z : ℚ) (N p : ℕ)
    (j : Fin (oddLowerPairedSize N p)) (r : Fin (n N)) : ℚ :=
  let ell := ((Fintype.equivFin ↥(oddLowerPairSet N p)).symm j).val
  (p : ℚ) * (rawEntryRat z N r.val ell + rawEntryRat z N r.val (p + ell))

def oddLowerPhysicalColumn (z : ℚ) (N p : ℕ)
    (j : oddLowerPhysicalIndex N p) (r : Fin (n N)) : ℚ :=
  oddPhysicalColumn p (oddLowerRetainedVector z N p) (oddLowerPairedVector z N p)
    (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j)
    (fun j : Fin 0 => Fin.elim0 j) j r

theorem oddLowerPhysicalColumn_retained {N p : ℕ} [hpPrime : Fact p.Prime]
    (z : ℚ) (j : ↥(oddLowerRetainedSet N p)) (r : Fin (n N)) :
    oddLowerPhysicalColumn z N p (oddLowerRetainedTag j) r = rawEntryRat z N r.val j.val := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
  simp only [oddLowerPhysicalColumn, oddLowerRetainedTag, oddPhysicalColumn,
    oddLowerRetainedVector, Equiv.symm_apply_apply]
  field_simp [hpq]

theorem oddLowerPhysicalColumn_paired {N p : ℕ} [hpPrime : Fact p.Prime]
    (z : ℚ) (ell : ↥(oddLowerPairSet N p)) (r : Fin (n N)) :
    oddLowerPhysicalColumn z N p (oddLowerPairedTag ell) r =
      rawEntryRat z N r.val ell.val + rawEntryRat z N r.val (p + ell.val) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
  simp only [oddLowerPhysicalColumn, oddLowerPairedTag, oddPhysicalColumn,
    oddLowerPairedVector, Equiv.symm_apply_apply]
  field_simp [hpq]

theorem oddLowerRetainedVector_den_ne_zero {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : H N < p ^ 2) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddLowerRetainedSize N p)) (r : Fin (n N)) :
    ((oddLowerRetainedVector z N p j r).den : ZMod p) ≠ 0 := by
  let v := (Fintype.equivFin ↥(oddLowerRetainedSet N p)).symm j
  have hv := (Finset.mem_sdiff.mp v.property).1
  have hvL := (Finset.mem_Ico.mp hv).2
  have hvH : v.val < H N := by unfold L H at *; omega
  exact (rawEntryRat_prime_digit_reduction hp2 hH hvH z hz).1

theorem oddLowerPairedVector_den_ne_zero {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (j : Fin (oddLowerPairedSize N p)) (r : Fin (n N)) :
    ((oddLowerPairedVector z N p j r).den : ZMod p) ≠ 0 := by
  let ell := (Fintype.equivFin ↥(oddLowerPairSet N p)).symm j
  have hb := oddLowerPairSet_bounds hN hp ell.property
  have hhigh : p + ell.val < H N := by have := hb.2.2.2.1; unfold L H at *; omega
  exact rawEntryRat_pair_prime_scaled_den_ne_zero hp2 hN r.isLt hb.2.1
    hb.2.2.1 hhigh (Nat.le_of_lt hb.2.2.2.2) z hz

theorem oddLowerHighSet_sub_mem_pair {N p j : ℕ} (hj : j ∈ oddLowerHighSet N p) :
    j - p ∈ oddLowerPairSet N p ∧ p + (j - p) = j := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hj
  simpa using And.intro hell (rfl : p + ell = p + ell)

def oddLowerInverseCoeff {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N)
    (i : oddLowerPhysicalIndex N p) (j : ↥(Finset.Ico (b N) (L N))) : ℤ :=
  if hj : j.val ∈ oddLowerHighSet N p then
    let ell : ↥(oddLowerPairSet N p) := ⟨j.val - p, (oddLowerHighSet_sub_mem_pair hj).1⟩
    let low : ↥(oddLowerRetainedSet N p) :=
      ⟨ell.val, oddLowerPairSet_mem_retained hN hp ell.property⟩
    (if i = oddLowerPairedTag ell then 1 else 0) -
      (if i = oddLowerRetainedTag low then 1 else 0)
  else
    let keep : ↥(oddLowerRetainedSet N p) := ⟨j.val, Finset.mem_sdiff.mpr ⟨j.property, hj⟩⟩
    if i = oddLowerRetainedTag keep then 1 else 0

theorem rawEntryRat_eq_lower_physical_sum {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hp : 2 * p ≤ H N) (z : ℚ)
    (j : ↥(Finset.Ico (b N) (L N))) (r : Fin (n N)) :
    rawEntryRat z N r.val j.val =
      ∑ i : oddLowerPhysicalIndex N p,
        oddLowerPhysicalColumn z N p i r * (oddLowerInverseCoeff hN hp i j : ℚ) := by
  by_cases hj : j.val ∈ oddLowerHighSet N p
  · simp only [oddLowerInverseCoeff, dite_eq_left hj, Int.cast_sub, Int.cast_ite,
      Int.cast_one, Int.cast_zero, mul_sub, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [oddLowerPhysicalColumn_paired, oddLowerPhysicalColumn_retained,
      (oddLowerHighSet_sub_mem_pair hj).2]
    ring
  · simp only [oddLowerInverseCoeff, dite_eq_right hj, Int.cast_ite, Int.cast_one,
      Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, oddLowerPhysicalColumn_retained]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddLowerPhysical_loss_eq {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N) :
    min (2 * n N) (min (n N + oddLowerRetainedSize N p)
      (2 * oddLowerRetainedSize N p + oddLowerPairedSize N p + 0)) =
        oddLowerCountLoss N p := by
  have hd := oddLowerPairCount_le_pool hN hp
  simp only [oddLowerRetainedSize, oddLowerPairedSize, Fintype.card_coe,
    oddLowerRetainedSet_card hN hp, oddLowerPairSet_card hN hp, add_zero]
  unfold oddLowerCountLoss
  omega

theorem oddLowerPhysicalCombination_valuation_lower {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (g : oddLowerPhysicalIndex N p → Fin (n N) → ℤ) :
    -(oddLowerCountLoss N p : ℤ) ≤ padicValRat p
      (Matrix.det (Matrix.of fun r k : Fin (n N) =>
        ∑ i, oddLowerPhysicalColumn z N p i r * (g i k : ℚ))) := by
  have h := oddPhysicalCombination_valuation_lower
    (p := p) (n := n N) (R := oddLowerRetainedSize N p)
    (B := oddLowerPairedSize N p) (C := 0) (e := 0)
    (oddLowerRetainedVector z N p) (oddLowerPairedVector z N p)
    (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j)
    (fun j : Fin 0 => Fin.elim0 j) (fun i k => (g i k : ℚ))
    (oddLowerRetainedVector_den_ne_zero hp2 hH z hz)
    (oddLowerPairedVector_den_ne_zero hp2 hN hp z hz)
    (by intro j; exact Fin.elim0 j) (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)
    (by intro i k; simp only [Rat.den_intCast, Nat.cast_one]; exact one_ne_zero)
  simpa only [oddLowerPhysical_loss_eq hN hp, oddLowerPhysicalColumn] using h

theorem rawMinorRat_odd_lower_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    -(oddLowerCountLoss N p : ℤ) ≤ padicValRat p (rawMinorRat z N c) := by
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => rawEntryRat z N r.val (c k).val) =
        (Matrix.of fun r k : Fin (n N) => ∑ i : oddLowerPhysicalIndex N p,
          oddLowerPhysicalColumn z N p i r * (oddLowerInverseCoeff hN hp i (c k) : ℚ)) := by
    ext r k
    exact rawEntryRat_eq_lower_physical_sum hN hp z (c k) r
  rw [rawMinorRat, hmatrix]
  exact oddLowerPhysicalCombination_valuation_lower hp2 hN hp hH z hz
    (fun i k => oddLowerInverseCoeff hN hp i (c k))

theorem determinantRat_odd_lower_valuation {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(oddLowerCountLoss N p : ℤ) ≤ padicValRat p (determinantRat z N) := by
  rw [determinantRat_eq_sum_raw_choices]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro c hc
  have hminor := rawMinorRat_odd_lower_valuation hp2 hN hp hH z hz c
  have hint := int_prime_valuation_nonneg p (∏ k, rawFilterInt N (c k) k)
  simpa only [zero_add] using prime_mul_valuation_lower
    (((∏ k, rawFilterInt N (c k) k : ℤ) : ℚ)) (rawMinorRat z N c)
    0 (-(oddLowerCountLoss N p : ℤ)) (by omega) hint hminor

theorem determinantRat_odd_lower_loss {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hp : 2 * p ≤ H N) (hH : H N < p ^ 2)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hv : -(oddLowerCountLoss N p : ℝ) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
    exact_mod_cast determinantRat_odd_lower_valuation hp2 hN hp hH z hz
  rw [oddLowerCountLoss_eq N p hN hp] at hv
  simpa only [neg_mul] using hv

end InternalCatalan

end

end OAI
