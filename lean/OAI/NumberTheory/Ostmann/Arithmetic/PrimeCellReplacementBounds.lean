import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacementTests

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression

theorem realTestSum_error (N M : ℕ) [NeZero M] (lo hi Z main E : ℝ)
    (F : (ZMod M)ˣ → ℝ) (hF : ∀ u, 0 ≤ F u)
    (hmass : ∀ u : (ZMod M)ˣ, |residueMass N M u lo hi Z - main| ≤ E) :
    |realTestSum N M lo hi Z F - main * ∑ u : (ZMod M)ˣ, F u| ≤
      E * ∑ u : (ZMod M)ˣ, F u := by
  have he : realTestSum N M lo hi Z F - main * ∑ u : (ZMod M)ˣ, F u =
      ∑ u : (ZMod M)ˣ, (residueMass N M u lo hi Z - main) * F u := by
    rw [realTestSum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he]
  calc
    _ ≤ ∑ u : (ZMod M)ˣ, |(residueMass N M u lo hi Z - main) * F u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : (ZMod M)ˣ, E * F u := by
      apply Finset.sum_le_sum
      intro u _
      rw [abs_mul, abs_of_nonneg (hF u)]
      exact mul_le_mul_of_nonneg_right (hmass u) (hF u)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem complexTestSum_error (N M : ℕ) [NeZero M] (lo hi Z main E : ℝ)
    (F : (ZMod M)ˣ → ℂ)
    (hmass : ∀ u : (ZMod M)ˣ, |residueMass N M u lo hi Z - main| ≤ E) :
    ‖complexTestSum N M lo hi Z F - (main : ℂ) * ∑ u : (ZMod M)ˣ, F u‖ ≤
      E * ∑ u : (ZMod M)ˣ, ‖F u‖ := by
  have he : complexTestSum N M lo hi Z F - (main : ℂ) * ∑ u : (ZMod M)ˣ, F u =
      ∑ u : (ZMod M)ˣ, ((residueMass N M u lo hi Z - main : ℝ) : ℂ) * F u := by
    rw [complexTestSum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [Complex.ofReal_sub, sub_mul]
  rw [he]
  calc
    _ ≤ ∑ u : (ZMod M)ˣ, ‖((residueMass N M u lo hi Z - main : ℝ) : ℂ) * F u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u : (ZMod M)ˣ, E * ‖F u‖ := by
      apply Finset.sum_le_sum
      intro u _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hmass u) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
