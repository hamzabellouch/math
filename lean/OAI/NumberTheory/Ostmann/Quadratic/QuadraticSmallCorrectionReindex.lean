import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdRangeBridge
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticExtraDivisors

namespace OAI

/-! # The small-kernel conductor corrections use the actual shorter Jacobi matrices -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadraticGcdBlockCoeff_coprime {R D n : ℕ} (v : ℕ → ℂ)
    (hn : Odd n) (h : ¬ (2 * D).Coprime n) : quadraticGcdBlockCoeff R D v n = 0 := by
  have hD : ¬ D.Coprime n := by
    intro hd
    exact h ((Nat.coprime_two_left.mpr hn).mul_left hd)
  simp [quadraticGcdBlockCoeff, quadraticRangeCoeff, quadraticDivisibilityCoeff, hD]

theorem quadratic_extra_weighted_reindex (N E : ℕ) (hE : 0 < E)
    (v w : ℕ → ℂ) (m : ℤ) (H : ℕ → ℂ)
    (hv : ∀ n ∈ oddSquarefreeRange (2 * N), ¬ E.Coprime n → v n = 0)
    (hw : ∀ n ∈ oddSquarefreeRange (2 * N), ¬ E.Coprime n → w n = 0) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
          ∑ d ∈ (E * (s * t)).divisors, H d else 0) =
      ∑ e ∈ E.divisors, ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        H (e * d) * quadraticDivisorBilinear (2 * N) (2 * N) d v w m := by
  let A (s t : ℕ) : ℂ := v s * conj (w t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)
  have hz (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N))
      (he : ¬ E.Coprime (s * t)) : A s t = 0 := by
    by_cases hes : E.Coprime s
    · have het : ¬ E.Coprime t := fun hh => he (hes.mul_right hh)
      simp [A, hw t ht het]
    · simp [A, hv s hs hes]
  have heq : (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then A s t * ∑ d ∈ (E * (s * t)).divisors, H d else 0) =
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t then
          if E.Coprime (s * t) then ∑ d ∈ (E * (s * t)).divisors, A s t * H d else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hc : s.Coprime t
    · rw [ite_eq_left hc, ite_eq_left hc]
      by_cases he : E.Coprime (s * t)
      · rw [ite_eq_left he, Finset.mul_sum]
      · rw [ite_eq_right he, hz s hs t ht he, zero_mul]
    · rw [ite_eq_right hc, ite_eq_right hc]
  change (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then A s t * ∑ d ∈ (E * (s * t)).divisors, H d else 0) = _
  rw [heq, quadratic_extra_divisor_reindex N E hE (fun s t d => A s t * H d)]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  unfold quadraticDivisorBilinear
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : s.Coprime t ∧ d ∣ s * t
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases he : E.Coprime (s * t)
    · rw [ite_eq_left he]
      dsimp [A]
      ring
    · rw [ite_eq_right he]
      have hh := hz s hs t ht he
      dsimp [A] at hh
      rw [one_mul]
      rw [mul_assoc, mul_assoc] at hh
      calc
        0 = H (e * d) * 0 := by ring
        _ = _ := by rw [← hh]; ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp

theorem quadratic_gcd_small_correction_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (H : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        ((jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors, H d)) =
      ∑ e ∈ (2 * D).divisors, ∑ d ∈ Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2),
        H (e * d) * quadraticDivisorBilinear (2 * quadraticGcdBlockSize R D)
          (2 * quadraticGcdBlockSize R D) d
            (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m := by
  have hDpos := Nat.pos_of_ne_zero hD.ne_zero
  rw [quadratic_gcd_block_reindex hD ho v w
    (fun q => (jacobiSym m q : ℂ) * ∑ d ∈ (2 * D * q).divisors, H d)]
  rw [quadratic_coprime_kernel_sum (2 * quadraticGcdBlockSize R D)
    (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w)
    (fun q => (jacobiSym m q : ℂ) * ∑ d ∈ (2 * D * q).divisors, H d)]
  rw [← quadratic_extra_weighted_reindex _ (2 * D) (by positivity : 0 < 2 * D)
    (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m H
    (fun n hn h => quadraticGcdBlockCoeff_coprime v (Finset.mem_filter.mp hn).2.1 h)
    (fun n hn h => quadraticGcdBlockCoeff_coprime w (Finset.mem_filter.mp hn).2.1 h)]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : s.Coprime t
  · rw [ite_eq_left hc, ite_eq_left hc,
      jacobiSym.mul_right' m (Finset.mem_filter.mp hs).2.2.ne_zero
        (Finset.mem_filter.mp ht).2.2.ne_zero, Int.cast_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

end Ostmann

end OAI
