import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterCharacter

namespace OAI

/-! # A fixed signed mean yields a positive population with large character bias -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_bias_population {ι : Type*} (S : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ i ∈ S, f i ≤ 1)
    (hsum : (S.card : ℝ) * c ≤ ∑ i ∈ S, f i) :
    (S.card : ℝ) * c / 2 ≤ ((S.filter fun i => c / 2 ≤ f i).card : ℝ) := by
  have hpoint (i : ι) (hi : i ∈ S) : f i ≤ c / 2 + if c / 2 ≤ f i then 1 else 0 := by
    split_ifs with h
    · linarith [hf i hi]
    · linarith
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_filter, mul_one] at hh
  linarith

noncomputable def orientedPrimeMean (P : Finset ℕ) (ε : ℕ → ℝ) (t : ℕ → ℤ) (x : ℤ) : ℝ :=
  (∑ p ∈ P, orientedQuadraticValue ε t x p) / P.card

theorem orientedPrimeMean_le_one (P : Finset ℕ) (ε : ℕ → ℝ) (t : ℕ → ℤ)
    (x : ℤ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) : orientedPrimeMean P ε t x ≤ 1 := by
  by_cases hP : P.Nonempty
  · have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
    apply (div_le_one hcard).mpr
    have hh : (∑ p ∈ P, orientedQuadraticValue ε t x p) ≤ ∑ _p ∈ P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases orientedQuadraticValue_ternary ε t x p (hε p hp) with h | h | h <;> rw [h] <;> norm_num
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hh
  · simp only [orientedPrimeMean, Finset.not_nonempty_iff_eq_empty.mp hP,
      Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero, zero_le_one]

theorem orientedPrimeMean_sum_lower (P : Finset ℕ) (S : Finset ℤ)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) (c : ℝ) (hP : 0 < P.card)
    (hmean : ∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) :
    (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedPrimeMean P ε t x := by
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hh := Finset.sum_le_sum hmean
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  simp only [orientedPrimeMean, ← Finset.sum_div]
  apply (le_div_iff₀ hcard).mpr
  rw [Finset.sum_comm]
  nlinarith only [hh]

theorem commonCenter_biased_population (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ℤ) (ε : ℕ → ℝ) (t : ℕ → ℤ) (m : ℕ) (h : ℤ) (c : ℝ)
    (hc : 0 ≤ c) (hm : 0 < m) (hcard : 0 < P.card)
    (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (hmp : ∀ p ∈ P, m < p)
    (ht : ∀ (p : ℕ) (hp : p ∈ P), let _ : Fact p.Prime := ⟨hP p hp⟩
      (t p : ZMod p) = (h : ZMod p) / (m : ZMod p))
    (hmean : ∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) :
    ∃ U ⊆ S, (S.card : ℝ) * c / 2 ≤ (U.card : ℝ) ∧
      ∀ x ∈ U, c / 2 ≤ ‖quadraticPrimeMean P (commonCenterOrientation ε m) ((m : ℤ) * x - h)‖ := by
  let U := S.filter fun x => c / 2 ≤ orientedPrimeMean P ε t x
  refine ⟨U, Finset.filter_subset _ _, ?_, ?_⟩
  · exact finite_bias_population S _ c hc
      (fun x _ => orientedPrimeMean_le_one P ε t x hε)
      (orientedPrimeMean_sum_lower P S ε t c hcard hmean)
  · intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    rw [quadraticPrimeMean_commonCenter P hP ε t m h x hm hmp ht, Complex.norm_real]
    exact hh.trans (le_abs_self _)

end Ostmann

end OAI
