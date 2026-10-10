import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDilationPrimes

namespace OAI

/-! # Quantitative row enlargement using the constructed prime family -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_dyadic_dilation (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ M N Q : ℕ, 0 < M → 0 < N →
      C * ((2 * (M : ℝ) * N) ^ δ) ≤ Q → ∀ U : ℝ, 0 ≤ U →
      QuadraticRowBound (quadraticWideRows (Q * M)) N U →
      QuadraticRowBound ((oddSquarefreeRange (2 * M)).filter (M ≤ ·)) N (4 * U) := by
  obtain ⟨C, hC, hc⟩ := quadratic_dilation_prime_supply δ hδ
  refine ⟨C, hC, ?_⟩
  intro M N Q hM hN hQ U hU hbound
  have hX : 0 < 2 * M * N := by positivity
  obtain ⟨hQ₂, hcount⟩ := hc (2 * M * N) Q hX
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hQ)
  have hNlog : Nat.log 2 N ≤ Nat.log 2 (2 * M * N) :=
    Nat.log_mono_right (by nlinarith)
  have hMlog : Nat.log 2 (2 * M) ≤ Nat.log 2 (2 * M * N) :=
    Nat.log_mono_right (by nlinarith)
  have hlogpos : 1 ≤ Nat.log 2 (2 * M * N) :=
    Nat.le_log_of_pow_le (by norm_num) (by norm_num; nlinarith)
  apply quadratic_prime_dilation (P := sizePrimeBand Q) (R := 2 * M)
    (fun p hp => (mem_sizePrimeBand.mp hp).1) (by omega)
    (fun m hm => ?_) (fun p hp m hm hpm => ?_)
    (by omega) hU hbound
  · have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    exact hi
  · obtain ⟨hp, hpQ, hp2Q⟩ := mem_sizePrimeBand.mp hp
    exact quadratic_prime_dilation_image hQ₂ hp hpQ hp2Q hm hpm

end Ostmann

end OAI
