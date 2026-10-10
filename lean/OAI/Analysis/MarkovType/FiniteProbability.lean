import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  sum_mass : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def expect (μ : FiniteLaw Ω) (F : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * F ω

def prob (μ : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then μ.mass ω else 0

def vexpect {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (μ : FiniteLaw Ω) (F : Ω → V) : V :=
  ∑ ω, μ.mass ω • F ω

theorem expect_nonneg (μ : FiniteLaw Ω) {F : Ω → ℝ} (hF : ∀ ω, 0 ≤ F ω) :
    0 ≤ μ.expect F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.mass_nonneg ω) (hF ω)

theorem expect_mono (μ : FiniteLaw Ω) {F G : Ω → ℝ} (hFG : ∀ ω, F ω ≤ G ω) :
    μ.expect F ≤ μ.expect G :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hFG ω) (μ.mass_nonneg ω)

@[simp] theorem expect_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.sum_mass, one_mul]

end FiniteLaw

end MarkovSuperreflexivity

end

end OAI
