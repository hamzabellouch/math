import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothed
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareRemoval
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeKernel

namespace OAI

namespace Ostmann.QuadraticSieve

theorem odd_square_jacobi_weight (u v d q : ℕ) [NeZero d] [NeZero q] (z : ℂ) :
    (if Odd (u ^ 2 * v) then (jacobiSym ((u ^ 2 * v : ℕ) : ℤ) (d ^ 2 * q) : ℂ) * z else 0) =
      if Nat.Coprime v (2 * d) then (jacobiSym (v : ℤ) q : ℂ) *
        (if Nat.Coprime u (2 * q * d) then z else 0) else 0 := by
  have hdu : (u : ℤ).gcd (d ^ 2 * q : ℕ) = 1 ↔ Nat.Coprime u d ∧ Nat.Coprime u q := by
    simp only [Int.gcd_natCast_natCast, ← Nat.coprime_iff_gcd_eq_one,
      Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by norm_num : 0 < 2)]
  have hdv : (v : ℤ).gcd (d : ℤ) = 1 ↔ Nat.Coprime v d := by
    simp only [Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one]
  have hchar : jacobiSym ((u ^ 2 * v : ℕ) : ℤ) (d ^ 2 * q) =
      if Nat.Coprime u d ∧ Nat.Coprime u q then
        (if Nat.Coprime v d then jacobiSym (v : ℤ) q else 0) else 0 := by
    rw [Nat.cast_mul, Nat.cast_pow, jacobi_square_mul_left,
      jacobi_square_mul_right]
    simp only [hdu, hdv]
  rw [hchar]
  simp only [Nat.odd_mul, Nat.odd_pow_iff (by decide : 2 ≠ 0),
    Nat.coprime_mul_iff_right, Nat.coprime_two_right]
  split_ifs <;> simp_all

theorem odd_kernel_cutoff_reindex (W : ℕ → ℂ)
    (hW : Summable (fun n : {n : ℕ // 0 < n} => W n.val))
    (K d q : ℕ) [NeZero d] [NeZero q] :
    (∑' n : {n : ℕ // 0 < n}, if squarefreeKernel n.val ≤ K then
      (if Odd n.val then (jacobiSym (n.val : ℤ) (d ^ 2 * q) : ℂ) * W n.val else 0) else 0) =
      ∑' v : {v : ℕ // Squarefree v}, if v.val ≤ K ∧ Nat.Coprime v.val (2 * d) then
        (jacobiSym (v.val : ℤ) q : ℂ) *
          ∑' u : {u : ℕ // 0 < u}, if Nat.Coprime u.val (2 * q * d) then
            W (u.val ^ 2 * v.val) else 0 else 0 := by
  have hs : Summable (fun n : {n : ℕ // 0 < n} =>
      if Odd n.val then (jacobiSym (n.val : ℤ) (d ^ 2 * q) : ℂ) * W n.val else 0) := by
    apply hW.norm.of_norm_bounded
    intro n
    split_ifs
    · rcases jacobiSym.trichotomy (n.val : ℤ) (d ^ 2 * q) with h | h | h <;> simp [h]
    · simp
  have hcut := tsum_positive_kernel_le
    (fun n => if Odd n then (jacobiSym (n : ℤ) (d ^ 2 * q) : ℂ) * W n else 0) hs K
  calc
    _ = ∑' v : {v : ℕ // Squarefree v}, if v.val ≤ K then
        ∑' u : {u : ℕ // 0 < u}, if Odd (u.val ^ 2 * v.val) then
          (jacobiSym ((u.val ^ 2 * v.val : ℕ) : ℤ) (d ^ 2 * q) : ℂ) *
            W (u.val ^ 2 * v.val) else 0 else 0 := hcut
    _ = _ := by
      apply tsum_congr
      intro v
      by_cases hv : v.val ≤ K
      · rw [ite_eq_left hv]
        have heq : (∑' u : {u : ℕ // 0 < u}, if Odd (u.val ^ 2 * v.val) then
            (jacobiSym ((u.val ^ 2 * v.val : ℕ) : ℤ) (d ^ 2 * q) : ℂ) *
              W (u.val ^ 2 * v.val) else 0) =
            ∑' u : {u : ℕ // 0 < u}, if Nat.Coprime v.val (2 * d) then
              (jacobiSym (v.val : ℤ) q : ℂ) *
                (if Nat.Coprime u.val (2 * q * d) then W (u.val ^ 2 * v.val) else 0) else 0 :=
          tsum_congr (fun u => odd_square_jacobi_weight u.val v.val d q (W (u.val ^ 2 * v.val)))
        rw [heq]
        by_cases hc : Nat.Coprime v.val (2 * d)
        · simp only [ite_eq_left hc, ite_eq_left (show v.val ≤ K ∧ Nat.Coprime v.val (2 * d) from ⟨hv, hc⟩), tsum_mul_left]
        · simp only [ite_eq_right hc, ite_eq_right (fun h : v.val ≤ K ∧
            Nat.Coprime v.val (2 * d) => hc h.2), tsum_zero]
      · simp only [hv, false_and, ite_false]

end Ostmann.QuadraticSieve

end OAI
