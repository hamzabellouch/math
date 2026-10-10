import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import OAI.NumberTheory.Ostmann.Construction.FiniteFrequencyExpansion

namespace OAI

/-! # Exact Möbius removal of the square-part coprimality condition -/

namespace Ostmann

open scoped BigOperators

private theorem sum_moebius_complex (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  have h' : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then (1 : ℤ) else 0 := by simpa only [ArithmeticFunction.one_apply] using h
  exact_mod_cast h'

theorem coprime_moebius_sum {M : ℕ} (hM : 0 < M) (w : ℕ) :
    (if w.Coprime M then (1 : ℂ) else 0) =
      ∑ P ∈ M.divisors, if P ∣ w then (ArithmeticFunction.moebius P : ℂ) else 0 := by
  classical
  have hg : Nat.gcd M w ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left w hM)
  have hs : M.divisors.filter (fun P => P ∣ w) = (Nat.gcd M w).divisors := by
    ext P
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, hg⟩, fun h => ⟨⟨h.1.1, hM.ne'⟩, h.1.2⟩⟩
  rw [← Finset.sum_filter, hs, sum_moebius_complex]
  congr 1
  exact propext (Nat.coprime_comm.trans Iff.rfl)

/-- This form allows the summation index to carry all the other frequency
parameters while `w` extracts only the square part. -/
theorem sum_coprime_moebius {ι : Type*} (S : Finset ι) (w : ι → ℕ) (a : ι → ℂ)
    {M : ℕ} (hM : 0 < M) :
    (∑ i ∈ S, a i * (if (w i).Coprime M then 1 else 0)) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ i ∈ S with P ∣ w i, a i := by
  classical
  simp_rw [coprime_moebius_sum hM, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem quadratic_square_removal (S : Finset ℕ) (a : ℕ → ℂ)
    {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic) :
    (∑ w ∈ S, a w * χ ((w : ZMod M) ^ 2)) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ w ∈ S with P ∣ w, a w := by
  simp_rw [quadratic_character_square χ hχ]
  exact sum_coprime_moebius S id a hM

theorem squarefree_frequency_moebius_expansion (L U : ℕ) (hL : 0 < L)
    {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic)
    (F : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 U, χ (u : ZMod M) * F u) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ z ∈ frequencyTriples L U with P ∣ z.2.2,
          χ (z.1 : ZMod M) * χ (z.2.1 : ZMod M) * F (z.1 * z.2.1 * z.2.2 ^ 2) := by
  rw [sum_squarefree_frequencies L U hL]
  simp_rw [quadratic_character_frequency χ hχ]
  have hs := sum_coprime_moebius (frequencyTriples L U) (fun z => z.2.2)
    (fun z => χ (z.1 : ZMod M) * χ (z.2.1 : ZMod M) * F (z.1 * z.2.1 * z.2.2 ^ 2)) hM
  rw [← hs]
  apply Finset.sum_congr rfl
  intro z hz
  ring

end Ostmann

end OAI
