import OAI.NumberTheory.JointDickman.Amplification.IntervalSquareBound

namespace OAI

/-! # The local residue-histogram Fourier estimate, manuscript (39) -/

namespace JointDickman
open Finset MeasureTheory

theorem histogram_fourier_integral_bound {q : ℕ} [NeZero q]
    {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (V : ℝ → (ZMod q)ˣ → ℂ) (F : ℝ → ℂ)
    (hF : ∀ x ∈ Set.Icc a b, ‖F x‖ ≤ M)
    (hVI : ∀ r, IntervalIntegrable (fun x => V x r*F x) volume a b)
    (hVIsq : ∀ r, IntervalIntegrable (fun x => ‖V x r*F x‖^2) volume a b)
    (hVsq : ∀ r, IntervalIntegrable (fun x => ‖V x r‖^2) volume a b) :
    (∑ h : ZMod q,
      ‖unitResidueFourier (fun r => ∫ x in a..b, V x r*F x) h/(q.totient : ℂ)‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*(b-a)*M^2*
        ((1/(q.totient : ℝ))*∑ r : (ZMod q)ˣ, ∫ x in a..b, ‖V x r‖^2) := by
  have hL : 0 ≤ b-a := sub_nonneg.mpr hab
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hper (r : (ZMod q)ˣ) : ‖∫ x in a..b, V x r*F x‖^2 ≤
      (b-a)*M^2*(∫ x in a..b, ‖V x r‖^2) := by
    refine (interval_norm_integral_square_le hab (hVI r) (hVIsq r)).trans ?_
    have hh : (∫ x in a..b, ‖V x r*F x‖^2) ≤ M^2*(∫ x in a..b, ‖V x r‖^2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hab (hVIsq r) ((hVsq r).const_mul _)
      intro x hx
      rw [norm_mul,mul_pow,mul_comm (M^2)]
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) hM).mpr (hF x hx)) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hh hL).trans_eq (by ring)
  rw [normalizedUnitResidue_fourier_parseval]
  calc
    _ ≤ ((q : ℝ)/(q.totient : ℝ))*((1/(q.totient : ℝ))*
        ∑ r : (ZMod q)ˣ, (b-a)*M^2*(∫ x in a..b, ‖V x r‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg q) hφ.le)
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hper r)) (by positivity)
    _ = _ := by rw [← mul_sum]; ring

end JointDickman

end OAI
