import OAI.Analysis.IrrationalRotation.Analysis.FejerKernel

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Invariant233.Fejer

theorem difference_pair_sum_nat (N r : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
      if (k : ℤ) - (l : ℤ) = (r : ℤ) then (1 : ℂ) else 0) = (N - r : ℕ) := by
  rw [Finset.sum_comm]
  have hinner (l : ℕ) :
      (∑ k ∈ Finset.range N,
        if (k : ℤ) - (l : ℤ) = (r : ℤ) then (1 : ℂ) else 0) =
      if l + r < N then 1 else 0 := by
    have heq (k : ℕ) : ((k : ℤ) - (l : ℤ) = (r : ℤ)) ↔ k = l + r := by omega
    simp_rw [heq]
    simp
  simp_rw [hinner]
  rw [Finset.sum_boole]
  have hfilter : (Finset.range N).filter (fun l => l + r < N) = Finset.range (N - r) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]

theorem difference_pair_sum_neg (N : ℕ) (r : ℤ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
      if (k : ℤ) - (l : ℤ) = -r then (1 : ℂ) else 0) =
    ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
      if (k : ℤ) - (l : ℤ) = r then (1 : ℂ) else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have heq : ((l : ℤ) - (k : ℤ) = -r) ↔ (k : ℤ) - (l : ℤ) = r := by omega
  simp only [heq]

theorem coefficient_eq_natAbs (N : ℕ) (r : ℤ) :
    coefficient N r = ((N - r.natAbs : ℕ) : ℂ) / (N : ℂ) := by
  rw [coefficient_expansion, div_eq_mul_inv, mul_comm]
  congr 1
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg r
  · simpa using difference_pair_sum_nat N n
  · rw [difference_pair_sum_neg]
    simpa using difference_pair_sum_nat N n

theorem coefficient_eq_triangular (N : ℕ) (r : ℤ) :
    coefficient N r =
      if r.natAbs < N then 1 - (r.natAbs : ℂ) / (N : ℂ) else 0 := by
  rw [coefficient_eq_natAbs]
  split_ifs with h
  · rw [Nat.cast_sub (Nat.le_of_lt h)]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]
    simp

@[simp] theorem coefficient_size_zero (r : ℤ) : coefficient 0 r = 0 := by
  simp [coefficient_eq_natAbs]

theorem coefficient_nonneg_real (N : ℕ) (r : ℤ) :
    coefficient N r = (coefficient N r).re ∧ 0 ≤ (coefficient N r).re := by
  rw [coefficient_eq_natAbs]
  simp only [Complex.div_natCast_re, Complex.natCast_re, Complex.ofReal_div,
    Complex.ofReal_natCast]
  constructor
  · norm_cast
  · positivity

theorem mem_frequencies_iff_natAbs_lt (N : ℕ) (r : ℤ) :
    r ∈ frequencies N ↔ r.natAbs < N := by
  rw [frequencies, Finset.mem_Ioo, ← abs_lt, ← Int.natCast_natAbs, Nat.cast_lt]

theorem coefficient_eq_on_frequencies {N : ℕ} {r : ℤ} (hr : r ∈ frequencies N) :
    coefficient N r = 1 - (r.natAbs : ℂ) / (N : ℂ) := by
  rw [coefficient_eq_triangular, ite_eq_left ((mem_frequencies_iff_natAbs_lt N r).mp hr)]

theorem kernel_eq_triangular_fourier_sum (N : ℕ) (t : Circle) :
    (kernel N t : ℂ) = ∑ r ∈ frequencies N,
      (1 - (r.natAbs : ℂ) / (N : ℂ)) * fourier r t := by
  rw [kernel_eq_finite_fourier_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [coefficient_eq_on_frequencies hr]

theorem sum_triangular_coefficients (N : ℕ) :
    (∑ r ∈ frequencies N, (1 - (r.natAbs : ℂ) / (N : ℂ))) = N := by
  have h := kernel_eq_triangular_fourier_sum N 0
  simpa only [kernel_zero, Complex.ofReal_natCast, fourier_eval_zero, mul_one] using h.symm

end Invariant233.Fejer

end

end OAI
