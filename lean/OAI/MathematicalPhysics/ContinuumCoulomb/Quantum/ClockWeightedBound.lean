import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.ClockPathBound

namespace OAI

/-! Fixed-weight clock bounds retain a strict completeness/soundness margin. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem norm_add_sq_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

theorem norm_add_sq_four {E : Type*} [NormedAddCommGroup E] (a b : E) :
    4*‖a+b‖^2 ≤ 5*‖a‖^2+20*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-4*‖b‖)]

theorem norm_add_sq_three {E : Type*} [NormedAddCommGroup E] (a b : E) :
    3*‖a+b‖^2 ≤ 4*‖a‖^2+12*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-3*‖b‖)]

theorem clock_path_weighted_mass_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (T : ℕ) :
    4*(∑ i ∈ Finset.range (T+1), ‖f i‖^2) ≤
      5*(T+1:ℝ)*‖f 0‖^2+20*T*(T+1:ℝ)*clockPathEnergy f T := by
  have hb (i : ℕ) (hi : i ∈ Finset.range (T+1)) :
      4*‖f i‖^2 ≤ 5*‖f 0‖^2+20*(T:ℝ)*clockPathEnergy f T := by
    have ha := clock_path_anchor_bound f T i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    have h := norm_add_sq_four (f 0) (f i-f 0)
    have he : f 0+(f i-f 0) = f i := by abel
    rw [he] at h
    linarith
  calc
    4*(∑ i ∈ Finset.range (T+1), ‖f i‖^2) =
        ∑ i ∈ Finset.range (T+1), 4*‖f i‖^2 := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (T+1),
        (5*‖f 0‖^2+20*(T:ℝ)*clockPathEnergy f T) := Finset.sum_le_sum hb
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      push_cast
      ring

end ContinuumCoulomb

end

end OAI
