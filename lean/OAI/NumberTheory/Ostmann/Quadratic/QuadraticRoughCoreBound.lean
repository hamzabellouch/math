import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOffDiagonalError

namespace OAI

/-! # The actual rough moment reduces to its finite off-diagonal core -/

namespace Ostmann

theorem quadratic_rough_core_bound {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 1 ≤ M → 1 ≤ N →
      (K : ℝ) ≤ ((M : ℝ) * N) ^ 3 →
      2 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ δ) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ,
      quadraticRoughEnergy M N K v ≤
        (3 * M + C / (((M : ℝ) * N) ^ P)) * quadraticSieveEnergy N v +
          ‖quadraticRoughOffDiagonalCore M N K (((M : ℝ) * N) ^ δ) v‖ := by
  obtain ⟨C, hC, hc⟩ := quadratic_rough_off_diagonal_arbitrary_power hδ P
  refine ⟨C, hC, ?_⟩
  intro M N K hM hN hK hcut v
  have he := hc M N K hM hN hK hcut v
  have ht := norm_add_le (quadraticRoughOffDiagonal M N K v -
    quadraticRoughOffDiagonalCore M N K (((M : ℝ) * N) ^ δ) v)
    (quadraticRoughOffDiagonalCore M N K (((M : ℝ) * N) ^ δ) v)
  rw [sub_add_cancel] at ht
  have hd := quadratic_rough_energy_off_diagonal M N K v
  nlinarith

theorem quadratic_dyadic_core_bound {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 1 ≤ M → 1 ≤ N → K < M →
      (K : ℝ) ≤ ((M : ℝ) * N) ^ 3 →
      2 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ δ) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ,
      (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
        ‖quadraticTransposeSum N v m‖ ^ 2) ≤
        (3 * M + C / (((M : ℝ) * N) ^ P)) * quadraticSieveEnergy N v +
          ‖quadraticRoughOffDiagonalCore M N K (((M : ℝ) * N) ^ δ) v‖ := by
  obtain ⟨C, hC, hc⟩ := quadratic_rough_core_bound hδ P
  exact ⟨C, hC, fun M N K hM hN hKM hK hcut v =>
    (quadratic_rough_dyadic_domination (by omega) hKM v).trans (hc M N K hM hN hK hcut v)⟩

end Ostmann

end OAI
