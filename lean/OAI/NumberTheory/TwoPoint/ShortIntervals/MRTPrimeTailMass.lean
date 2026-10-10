import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands

namespace OAI

/-! Mertens mass on power-logarithmic prime tails, uniformly in the
exponent. This is the common finite prime range in both VK applications. -/

namespace TwoPointCorrelations

open Finset

noncomputable def mrtPrimePowerTail (a : ℝ) (X : ℕ) : Finset ℕ :=
  mrtPrimeBand (Real.exp ((Real.log (X:ℝ))^a)) X

theorem mrt_prime_power_tail_mass :
    ∃ C : ℝ, 0≤C ∧ ∀ a : ℝ, 0≤a → a≤1 → ∀ X : ℕ,
      1≤Real.log (X:ℝ) →
      (1-a)*Real.log (Real.log (X:ℝ))-C ≤
        ∑ p ∈ mrtPrimePowerTail a X, 1/(p:ℝ) := by
  obtain ⟨C,hC,hm⟩ := mrt_prime_band_mertens
  refine ⟨C,hC,?_⟩
  intro a ha ha1 X hL
  have hL0 : 0<Real.log (X:ℝ) := by linarith
  have hX0 : (0:ℝ)<X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL0)
  have hpow : 1≤(Real.log (X:ℝ))^a := Real.one_le_rpow hL ha
  have hP : 2≤Real.exp ((Real.log (X:ℝ))^a) := by
    linarith [Real.add_one_le_exp ((Real.log (X:ℝ))^a)]
  have hPX : Real.exp ((Real.log (X:ℝ))^a) ≤ (X:ℝ) := by
    calc
      _ ≤ Real.exp (Real.log (X:ℝ)) := Real.exp_le_exp.mpr
        (Real.rpow_le_self_of_one_le hL ha1)
      _ = _ := Real.exp_log hX0
  have hh := (abs_le.mp (hm _ _ hP hPX)).1
  rw [Real.log_exp,Real.log_rpow hL0] at hh
  change (1-a)*Real.log (Real.log (X:ℝ))-C ≤
    ∑ p ∈ mrtPrimeBand (Real.exp ((Real.log (X:ℝ))^a)) X, 1/(p:ℝ)
  linarith

end TwoPointCorrelations

end OAI
