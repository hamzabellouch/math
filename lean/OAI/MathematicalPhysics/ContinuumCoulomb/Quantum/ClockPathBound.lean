import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateUnitary
import Mathlib.Algebra.Order.Chebyshev

namespace OAI

/-! Elementary quantitative propagation estimates for the finite clock.
They compare every clock slice to its initial slice. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def clockPathEnergy {E : Type*} [NormedAddCommGroup E] (f : ℕ → E) (T : ℕ) : ℝ :=
  ∑ i ∈ Finset.range T, ‖f (i+1)-f i‖^2

theorem clockPathEnergy_nonneg {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (T : ℕ) : 0 ≤ clockPathEnergy f T :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem clock_path_anchor_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (T i : ℕ) (hi : i ≤ T) :
    ‖f i-f 0‖^2 ≤ (T:ℝ)*clockPathEnergy f T := by
  have ht : ∑ j ∈ Finset.range i, (f (j+1)-f j) = f i-f 0 := by
    exact Finset.sum_range_sub f i
  have hn : ‖f i-f 0‖ ≤ ∑ j ∈ Finset.range i, ‖f (j+1)-f j‖ := by
    rw [←ht]
    exact norm_sum_le _ _
  have hsq : ‖f i-f 0‖^2 ≤ (∑ j ∈ Finset.range i, ‖f (j+1)-f j‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range i) (f := fun j => ‖f (j+1)-f j‖)
  have he : (∑ j ∈ Finset.range i, ‖f (j+1)-f j‖^2) ≤ clockPathEnergy f T := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
    intro _ _ _
    positivity
  apply (hsq.trans hc).trans
  simp only [Finset.card_range]
  exact mul_le_mul (by exact_mod_cast hi) he (by positivity) (Nat.cast_nonneg T)

theorem clock_path_mass_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (T : ℕ) :
    (∑ i ∈ Finset.range (T+1), ‖f i‖^2) ≤
      2*(T+1:ℝ)*‖f 0‖^2 + 2*T*(T+1:ℝ)*clockPathEnergy f T := by
  have hb (i : ℕ) (hi : i ∈ Finset.range (T+1)) :
      ‖f i‖^2 ≤ 2*‖f 0‖^2 + 2*(T:ℝ)*clockPathEnergy f T := by
    have ha := clock_path_anchor_bound f T i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    have hn : ‖f i‖ ≤ ‖f i-f 0‖+‖f 0‖ := by
      simpa only [add_comm] using norm_le_insert' (f i) (f 0)
    have hs : ‖f i‖^2 ≤ (‖f i-f 0‖+‖f 0‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖f i-f 0‖-‖f 0‖)]
  apply (Finset.sum_le_sum hb).trans_eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
