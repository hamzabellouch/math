import OAI.NumberTheory.Catalan.Arithmetic.SmallOddPrimePartition

namespace OAI


noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem oddPhysicalCombination_expansion {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (g : oddPhysicalIndex R B C → Fin n → ℚ) :
    Matrix.det (Matrix.of fun r k : Fin n =>
      ∑ j, oddPhysicalColumn p U W I V a j r * g j k) =
      ∑ c : Fin n → oddPhysicalIndex R B C,
        (∏ k, g (c k) k) *
          Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) := by
  calc
    _ = ∑ c : Fin n → oddPhysicalIndex R B C,
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k, oddPhysicalColumn p U W I V a (c k) (σ k) * g (c k) k := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem oddPhysicalMinor_eq_zero_of_not_injective {n R B C e : ℕ} (p : ℕ)
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (c : Fin n → oddPhysicalIndex R B C)
    (hc : ¬ Function.Injective c) :
    Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r) = 0 := by
  simp only [Function.Injective] at hc
  push Not at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply, hij]

theorem oddPhysicalCombination_valuation_lower {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ) (g : oddPhysicalIndex R B C → Fin n → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (ha : ∀ j l, ((a j l).den : ZMod p) ≠ 0)
    (hg : ∀ j k, ((g j k).den : ZMod p) ≠ 0) :
    -((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ) ≤
      padicValRat p (Matrix.det (Matrix.of fun r k : Fin n =>
        ∑ j, oddPhysicalColumn p U W I V a j r * g j k)) := by
  rw [oddPhysicalCombination_expansion]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro c hc
  by_cases hcinj : Function.Injective c
  · have hm := oddPhysicalMinor_valuation_lower U W I V a hU hW hI hV ha c hcinj
    have hgprod : 0 ≤ padicValRat p (∏ k, g (c k) k) := by
      simpa only [mul_zero] using prime_prod_valuation_lower Finset.univ
        (fun k => g (c k) k) 0 (by omega)
        (fun k _ => rational_valuation_nonneg_of_den_ne_zero (hg (c k) k))
    simpa only [zero_add] using prime_mul_valuation_lower
      (∏ k, g (c k) k)
      (Matrix.det (Matrix.of fun r k => oddPhysicalColumn p U W I V a (c k) r))
      0 (-((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ))
      (by omega) hgprod hm
  · rw [oddPhysicalMinor_eq_zero_of_not_injective p U W I V a c hcinj,
      mul_zero, padicValRat.zero]
    omega

end InternalCatalan

end

end OAI
