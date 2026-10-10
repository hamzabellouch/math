import OAI.Combinatorics.Progressions.Lattices.HalfResidueDescent

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_polynomial_residue_descent_size (A B : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {σ : Type*} [Fintype σ] (p q : ℝ),
      0 ≤ p → 0 ≤ q → q ≤ (p + 2) ^ A →
      ∀ (N : σ → ℕ) (M P : ℕ) (J : σ → ℕ) (ε δ : ℝ),
      (M : ℝ) ≤ Real.exp ((p + 2) ^ A) → (P : ℝ) ≤ Real.exp ((p + 2) ^ A) →
      (∀ i, (J i : ℝ) ≤ Real.exp ((p + 2) ^ A)) →
      (Fintype.card σ : ℝ) ≤ Real.exp ((p + 2) ^ A) →
      0 < ε → 0 < δ → ε⁻¹ ≤ Real.exp ((p + 2) ^ A) → δ⁻¹ ≤ Real.exp ((p + 2) ^ A) →
      (∀ i, Real.exp ((p + 2) ^ K) ≤ (N i : ℝ)) →
      (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) ∧
      (∀ i, 8 ≤ δ * (N i : ℝ)) ∧
      (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 := by
  let X : Polynomial ℕ := (Polynomial.X + 2) ^ A
  let R : Polynomial ℕ := 6 * ((X + Polynomial.C B) ^ B + X) + 8
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget R
  refine ⟨K, hK, ?_⟩
  intro σ _ p q hp hq hqp N M P J ε δ hM hP hJ hcard hε hδ hεinv hδinv hN
  let L := ((p + 2) ^ A + B) ^ B + (p + 2) ^ A
  have hbase : 0 ≤ (p + 2) ^ A := by positivity
  have hterm : 0 ≤ ((p + 2) ^ A + B) ^ B := by positivity
  have hL : 0 ≤ L := add_nonneg hterm hbase
  have hbaseL : (p + 2) ^ A ≤ L := le_add_of_nonneg_left hterm
  have hstepL : (q + B) ^ B ≤ L := by
    exact (pow_le_pow_left₀ (by positivity) (add_le_add hqp (le_refl (B : ℝ))) B).trans
      (le_add_of_nonneg_right hbase)
  have hbudgetL : 6 * L + 8 ≤ (p + 2) ^ K := by
    simpa [R, X, L, Polynomial.eval₂_pow] using hbudget p hp
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hsize : ∀ i, 8 * (Real.exp L) ^ 6 ≤ (N i : ℝ) := by
    intro i
    calc
      8 * (Real.exp L) ^ 6 ≤ Real.exp 8 * (Real.exp L) ^ 6 :=
        mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = Real.exp (6 * L + 8) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        norm_num
        ring
      _ ≤ Real.exp ((p + 2) ^ K) := Real.exp_le_exp.mpr hbudgetL
      _ ≤ (N i : ℝ) := hN i
  have hexp : Real.exp ((p + 2) ^ A) ≤ Real.exp L := Real.exp_le_exp.mpr hbaseL
  exact residue_descent_size_bounds N M P J (Real.exp L) (Real.exp ((q + B) ^ B)) ε δ
    (Real.one_le_exp hL) (Real.exp_le_exp.mpr hstepL) (hM.trans hexp) (hP.trans hexp)
    (fun i => (hJ i).trans hexp) (hcard.trans hexp) hε hδ (hεinv.trans hexp) (hδinv.trans hexp) hsize

end Erdos3

end

end OAI
