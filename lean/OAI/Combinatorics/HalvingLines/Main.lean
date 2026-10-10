import OAI.Combinatorics.HalvingLines.Perturbation

namespace OAI

open Filter Topology

namespace PlanarHalving

theorem halving_power :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε) := by
  obtain ⟨ε,hε,C,hbound⟩ := all_ranks_power
  refine ⟨ε,hε,C,2,?_⟩
  intro n heven hn P hP
  obtain ⟨m,hm⟩ := heven
  have hn' : n=2*m := by omega
  clear hm
  subst n
  obtain ⟨Q,hQ,hcount⟩ := Perturbation.generic_same_halvingCount hP
  rw [hcount,halvingCount_eq_middle_switchCount (by omega : 0 < m) Q hQ]
  exact hbound (2*m) (by omega) Q hQ m (by omega)
end PlanarHalving

namespace PlanarHalving

theorem power_bounds :
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) :=
  ⟨halving_power, all_ranks_power⟩

end PlanarHalving

end OAI
