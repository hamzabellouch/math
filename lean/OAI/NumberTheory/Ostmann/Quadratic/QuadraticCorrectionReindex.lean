import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformGauss
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSqrtCoefficients

namespace OAI

/-! # Exact pair-to-divisor rearrangement for the retained corrections -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_coprime_divisor_reindex (N : ℕ) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then ∑ d ∈ (s * t).divisors, F s t d else 0) =
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
  have hlocal (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N)) :
      (if s.Coprime t then ∑ d ∈ (s * t).divisors, F s t d else 0) =
      ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
    obtain ⟨hsr, _, hss⟩ := Finset.mem_filter.mp hs
    obtain ⟨htr, _, hst⟩ := Finset.mem_filter.mp ht
    have hq : s * t ≠ 0 := mul_ne_zero hss.ne_zero hst.ne_zero
    have hqtop : s * t ≤ (2 * N) ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul (Finset.mem_Icc.mp hsr).2
        (Finset.mem_Icc.mp htr).2
    have heq : (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d => d ∣ s * t) = (s * t).divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · intro h
        exact ⟨h.2, hq⟩
      · intro h
        have hd := Nat.mem_divisors.mpr h
        exact ⟨⟨Nat.pos_of_mem_divisors hd,
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h.1).trans hqtop⟩, h.1⟩
    by_cases hc : s.Coprime t
    · rw [ite_eq_left hc]
      have heq' : (Finset.Icc 1 ((2 * N) ^ 2)).filter
          (fun d => s.Coprime t ∧ d ∣ s * t) = (s * t).divisors := by
        convert heq using 1
        ext d
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hc, h.2⟩⟩
      rw [← Finset.sum_filter, heq']
    · simp [hc]
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
          if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_congr rfl (fun t ht => hlocal s hs t ht)
    _ = _ := by
      conv_lhs =>
        arg 2
        ext s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

theorem quadratic_sqrt_gauss_divisor (N d : ℕ) (v w : ℕ → ℂ) (m : ℤ) :
    quadraticGaussDivisorBilinear (2 * N) (2 * N) d
      (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m =
    ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        v s * conj (w t) * quadraticGaussMultiplier (s * t) *
        (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) /
          (Real.sqrt (s * t : ℕ) : ℂ) := by
  unfold quadraticGaussDivisorBilinear quadraticSqrtNormalize
  apply Finset.sum_congr rfl
  intro s _hs
  apply Finset.sum_congr rfl
  intro t _ht
  rw [map_div₀, Complex.conj_ofReal]
  have hr : (Real.sqrt (s * t : ℕ) : ℂ) =
      (Real.sqrt s : ℂ) * (Real.sqrt t : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg s), Complex.ofReal_mul]
  rw [hr]
  ring

end Ostmann

end OAI
