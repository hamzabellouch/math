import Mathlib.Algebra.Order.Chebyshev
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondError

namespace OAI

/-! # Summing the normalized Poisson remainder over a real coefficient block -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticCoprimeBlockPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (quadraticGcdPairs (2 * N) 1).filter (fun z => N ≤ z.1 ∧ N ≤ z.2)

noncomputable def quadraticBlockError (N : ℕ) (m : ℤ) (v : ℕ → ℂ)
    (E : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticCoprimeBlockPairs N,
    v z.1 * conj (v z.2) * quadraticGaussMultiplier (z.1 * z.2) *
      (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) * E (z.1 * z.2)

theorem quadratic_block_error_bound {N : ℕ} (hN : 2 ≤ N) (m : ℤ)
    (v : ℕ → ℂ) (E : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hE : ∀ q : ℕ, N ^ 2 ≤ q → q ≤ 4 * N ^ 2 → q ≠ 1 → ‖E q‖ ≤ T) :
    ‖quadraticBlockError N m v E‖ ≤ T * (2 * N) * quadraticSieveEnergy (2 * N) v := by
  let S := oddSquarefreeRange (2 * N)
  have hJ (n : ℕ) : ‖(jacobiSym m n : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy m n with hh | hh | hh <;> rw [hh] <;> norm_num
  have henergy : 0 ≤ quadraticSieveEnergy (2 * N) v :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpoint (z : ℕ × ℕ) (hz : z ∈ quadraticCoprimeBlockPairs N) :
      ‖v z.1 * conj (v z.2) * quadraticGaussMultiplier (z.1 * z.2) *
        (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) * E (z.1 * z.2)‖ ≤
        ‖v z.1‖ * ‖v z.2‖ * T := by
    obtain ⟨hz, hlo⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
    obtain ⟨hr₁, ho₁, hs₁⟩ := Finset.mem_filter.mp hz₁
    obtain ⟨hr₂, ho₂, hs₂⟩ := Finset.mem_filter.mp hz₂
    have hqlo : N ^ 2 ≤ z.1 * z.2 := by nlinarith [Nat.mul_le_mul hlo.1 hlo.2]
    have hqhi : z.1 * z.2 ≤ 4 * N ^ 2 := by
      nlinarith [Nat.mul_le_mul (Finset.mem_Icc.mp hr₁).2 (Finset.mem_Icc.mp hr₂).2]
    have hq1 : z.1 * z.2 ≠ 1 := by nlinarith
    have hg := quadraticGaussMultiplier_norm ((Nat.squarefree_mul hcop).mpr ⟨hs₁, hs₂⟩)
      (ho₁.mul ho₂)
    simp only [norm_mul, Complex.norm_conj, hg, mul_one]
    calc
      _ ≤ ‖v z.1‖ * ‖v z.2‖ * 1 * 1 * T := by
        gcongr
        · exact hJ z.1
        · exact hJ z.2
        · exact hE _ hqlo hqhi hq1
      _ = _ := by ring
  have hsub : quadraticCoprimeBlockPairs N ⊆ S.product S := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hcard : (S.card : ℝ) ≤ 2 * N := by
    have hh := Finset.card_le_card (Finset.filter_subset
      (s := Finset.Icc 1 (2 * N)) (p := fun n => Odd n ∧ Squarefree n))
    have hh' : S.card ≤ 2 * N := by simpa [S, oddSquarefreeRange] using hh
    exact_mod_cast hh'
  have hc : (∑ n ∈ S, ‖v n‖) ^ 2 ≤ (S.card : ℝ) * quadraticSieveEnergy (2 * N) v :=
    sq_sum_le_card_mul_sum_sq
  calc
    _ ≤ ∑ z ∈ quadraticCoprimeBlockPairs N, ‖v z.1‖ * ‖v z.2‖ * T :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ ≤ ∑ z ∈ S.product S, ‖v z.1‖ * ‖v z.2‖ * T :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = T * (∑ n ∈ S, ‖v n‖) ^ 2 := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ T * ((S.card : ℝ) * quadraticSieveEnergy (2 * N) v) :=
      mul_le_mul_of_nonneg_left hc hT
    _ = T * (S.card : ℝ) * quadraticSieveEnergy (2 * N) v := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hT) henergy

end Ostmann

end OAI
