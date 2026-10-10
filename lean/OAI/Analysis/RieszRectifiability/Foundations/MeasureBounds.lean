import Mathlib
import OAI.Analysis.RieszRectifiability.Model

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

def ADRegular {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r) ∧
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

def UniformlyRectifiable {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∃ M : ℝ≥0,
    ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ∃ g : (ball (0 : Ambient n) r) → Ambient d,
        LipschitzWith M g ∧
        ENNReal.ofReal (θ * r ^ n) ≤ μ (ball x r ∩ range g)

def RieszL2Bounded {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) : Prop :=
  ∃ C : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ,
    MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ ∧
      eLpNorm (truncated n μ ε f) 2 μ ≤ (C : ℝ≥0∞) * eLpNorm f 2 μ

def FullStatement : Prop :=
  ∀ d n : ℕ, 4 ≤ d → 2 ≤ n → n + 2 ≤ d →
    ∀ μ : Measure (Ambient d), μ.Regular →
      ADRegular n μ → RieszL2Bounded n μ → UniformlyRectifiable n μ

theorem admissibleRadius_pos {d : ℕ} {μ : Measure (Ambient d)} {r : ℝ}
    (h : AdmissibleRadius μ r) : 0 < r := h.1

theorem adRegular_constant_pos {d : ℕ} {n : ℕ} {μ : Measure (Ambient d)}
    (h : ADRegular n μ) : ∃ C : ℝ, 0 < C ∧ 1 ≤ C := by
  obtain ⟨C, hC, _⟩ := h
  exact ⟨C, lt_of_lt_of_le zero_lt_one hC, hC⟩

theorem kernel_self {d : ℕ} (n : ℕ) (x : Ambient d) : kernel n x x = 0 := by
  simp [kernel]

theorem kernel_antisymm {d : ℕ} (n : ℕ) (x y : Ambient d) :
    kernel n y x = -kernel n x y := by
  rw [kernel, kernel, norm_sub_rev, ← neg_sub x y, smul_neg]

end

end RieszRectifiability

end OAI
