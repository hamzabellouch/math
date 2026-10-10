import OAI.NumberTheory.Ostmann.Characters.PivotProductPrior

namespace OAI

/-! # Exact counterpart normalization under the original harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def counterpartRoleFactor {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n)) (i : Fin n) (p : P) : ℝ :=
  if (p : ℕ) ∈ Q (e.symm i) then 1 else 0

theorem counterpartRoleFactor_mem_Icc {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n)) (i : Fin n) (p : P) :
    counterpartRoleFactor P Q e i p ∈ Set.Icc (0 : ℝ) 1 := by
  unfold counterpartRoleFactor
  split_ifs <;> constructor <;> norm_num

/-- Every counterpart role restriction is a unary factor on its matched
actual prime. The normalizing constant and total prime product are exact. -/
theorem matched_harmonic_prior {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n)) (x : Fin n → P) :
    productPrior (fun i => primeSubsetPrior P (Q i)) (fun i => x (e i)) =
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ *
        ∏ i, counterpartRoleFactor P Q e i (x i) := by
  have hatom (i : Fin n) : primeSubsetPrior P (Q i) (x (e i)) =
      (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x (e i) : ℝ)⁻¹ *
        counterpartRoleFactor P Q e (e i) (x (e i)) := by
    simp only [primeSubsetPrior, counterpartRoleFactor, Equiv.symm_apply_apply]
    split_ifs <;> simp only [mul_one, mul_zero]
    ring
  unfold productPrior
  simp_rw [hatom]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Equiv.prod_comp e (fun i => (x i : ℝ)⁻¹),
    Equiv.prod_comp e (fun i => counterpartRoleFactor P Q e i (x i))]
  simp only [Finset.prod_inv_distrib]

theorem counterpartRoleFactor_norm {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n)) (i : Fin n) (p : P) :
    ‖(counterpartRoleFactor P Q e i p : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (counterpartRoleFactor_mem_Icc P Q e i p).1]
  exact (counterpartRoleFactor_mem_Icc P Q e i p).2

/-- Extract the reciprocal scale before summing external pivots. On the
stated product window the remaining ratio and all unary restrictions are
bounded by one. -/
theorem matched_harmonic_prior_normalized {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n)) (x : Fin n → P)
    (X : ℝ) (hX : 0 < X) (hprod : X ≤ ∏ i, (x i : ℝ)) :
    ∃ U : ℝ, U ∈ Set.Icc 0 1 ∧
      productPrior (fun i => primeSubsetPrior P (Q i)) (fun i => x (e i)) =
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * X⁻¹ * U ∧
      U = (X / (∏ i, (x i : ℝ))) * ∏ i, counterpartRoleFactor P Q e i (x i) := by
  let R := ∏ i, counterpartRoleFactor P Q e i (x i)
  have hR0 : 0 ≤ R := Finset.prod_nonneg (fun i _ => (counterpartRoleFactor_mem_Icc P Q e i (x i)).1)
  have hR1 : R ≤ 1 := Finset.prod_le_one₀
    (fun i _ => (counterpartRoleFactor_mem_Icc P Q e i (x i)).1)
    (fun i _ => (counterpartRoleFactor_mem_Icc P Q e i (x i)).2)
  have hprodpos : 0 < ∏ i, (x i : ℝ) := hX.trans_le hprod
  refine ⟨X / (∏ i, (x i : ℝ)) * R, ⟨by positivity, ?_⟩, ?_, rfl⟩
  · exact (mul_le_mul (div_le_one_of_le₀ hprod hprodpos.le) hR1 hR0 (by norm_num)).trans
      (by norm_num)
  · rw [matched_harmonic_prior]
    dsimp only [R]
    field_simp

end Ostmann

end OAI
