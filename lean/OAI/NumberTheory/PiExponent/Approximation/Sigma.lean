import Mathlib

namespace OAI

namespace PiExponent

theorem exists_small_rational_sigma
    (m : ℕ) (α β θ : ℝ) (hα : α < 1) (hβ : β < 1) (hθ : θ < 1) :
    ∃ σ : ℚ, 0 < (σ : ℝ) ∧
      (1 + 3 * (σ : ℝ)) ^ (m + 1) * α < 1 ∧
      (1 + 3 * (σ : ℝ)) ^ m * β < 1 ∧
      (1 + (σ : ℝ)) * θ < 1 := by
  have hopenα : IsOpen {s : ℝ | (1 + 3 * s) ^ (m + 1) * α < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopenβ : IsOpen {s : ℝ | (1 + 3 * s) ^ m * β < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopenθ : IsOpen {s : ℝ | (1 + s) * θ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopen : IsOpen {s : ℝ |
      (1 + 3 * s) ^ (m + 1) * α < 1 ∧
      (1 + 3 * s) ^ m * β < 1 ∧
      (1 + s) * θ < 1} :=
    hopenα.inter (hopenβ.inter hopenθ)
  have hzero : (0 : ℝ) ∈ {s : ℝ |
      (1 + 3 * s) ^ (m + 1) * α < 1 ∧
      (1 + 3 * s) ^ m * β < 1 ∧
      (1 + s) * θ < 1} := by
    simpa using And.intro hα (And.intro hβ hθ)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  obtain ⟨σ, hσ0, hσε⟩ := exists_rat_btwn hε
  have hσmem : (σ : ℝ) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ0]
    exact hσε
  exact ⟨σ, hσ0, hball hσmem⟩

end PiExponent

end OAI
