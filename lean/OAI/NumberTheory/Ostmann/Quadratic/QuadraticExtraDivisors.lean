import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeDivisors
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionReindex

namespace OAI

/-! # Removing the fixed conductor factor from the actual small-kernel divisors -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_extra_divisor_reindex (N E : ℕ) (hE : 0 < E)
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        if E.Coprime (s * t) then ∑ d ∈ (E * (s * t)).divisors, F s t d else 0
      else 0) =
    ∑ e ∈ E.divisors, ∑ f ∈ Finset.Icc 1 ((2 * N) ^ 2),
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ f ∣ s * t then
          if E.Coprime (s * t) then F s t (e * f) else 0
        else 0 := by
  have hlocal (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N)) :
      (if s.Coprime t then
        if E.Coprime (s * t) then ∑ d ∈ (E * (s * t)).divisors, F s t d else 0
       else 0) =
      ∑ e ∈ E.divisors, if s.Coprime t then
        ∑ f ∈ (s * t).divisors, if E.Coprime (s * t) then F s t (e * f) else 0
      else 0 := by
    have hst : 0 < s * t := Nat.mul_pos
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
    by_cases hc : s.Coprime t
    · simp only [ite_eq_left hc]
      by_cases he : E.Coprime (s * t)
      · simp only [ite_eq_left he]
        exact quadratic_coprime_divisor_sum hE hst he (F s t)
      · simp only [ite_eq_right he, Finset.sum_const_zero]
    · simp only [ite_eq_right hc, Finset.sum_const_zero]
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        ∑ e ∈ E.divisors, if s.Coprime t then
          ∑ f ∈ (s * t).divisors, if E.Coprime (s * t) then F s t (e * f) else 0
        else 0 := by
      exact Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun t ht => hlocal s hs t ht))
    _ = ∑ e ∈ E.divisors,
        ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
          if s.Coprime t then
            ∑ f ∈ (s * t).divisors, if E.Coprime (s * t) then F s t (e * f) else 0
          else 0 := by
      conv_lhs =>
        arg 2
        ext s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl (fun e _ => quadratic_coprime_divisor_reindex N
      (fun s t f => if E.Coprime (s * t) then F s t (e * f) else 0))

end Ostmann

end OAI
