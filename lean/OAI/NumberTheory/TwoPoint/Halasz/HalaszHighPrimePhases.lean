import OAI.NumberTheory.TwoPoint.Halasz.HalaszCosineMinorant
import OAI.NumberTheory.TwoPoint.Halasz.HalaszHighPrimeInput
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeTailMass

namespace OAI

/-! The high-frequency prime-repulsion step needs only three real prime
phases on the power-logarithmic tail, bounded uniformly over the
indicated height range. -/
namespace TwoPointCorrelations

open Finset Filter

theorem halasz_high_prime_of_three_phases
    (hphase : ∃ K : ℝ, ∀ᶠ X : ℕ in atTop,
      ∀ u : ℝ, (Real.log X)^20 ≤ |u| → |u| ≤ 2*X →
      ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        |∑ p ∈ mrtPrimePowerTail (27/40) X,
          Real.cos ((k:ℝ)*u*Real.log (p:ℝ))/(p:ℝ)| ≤ K) :
    HalaszHighPrimeInput := by
  obtain ⟨K,hphase⟩ := hphase
  obtain ⟨C,hC,hmass⟩ := mrt_prime_power_tail_mass
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (10240*((81/256)*C+(95/256)*K)))
  filter_upwards [hphase,hll,hlog.eventually (eventually_ge_atTop (1:ℝ))]
    with X hp hlarge hL
  intro u hu hux
  let P := mrtPrimePowerTail (27/40) X
  have hs : (13/40:ℝ)*Real.log (Real.log X)-C ≤ ∑ p ∈ P, 1/(p:ℝ) := by
    simpa only [show (1:ℝ)-27/40=13/40 by norm_num] using
      hmass (27/40) (by norm_num) (by norm_num) X hL
  have hsum (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
      |∑ p ∈ P, (1/(p:ℝ))*Real.cos ((k:ℝ)*(u*Real.log (p:ℝ)))| ≤ K := by
    simpa only [P,div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using
      hp u hu hux k hk hk3
  have h₁ := hsum 1 (by omega) (by omega)
  simp only [Nat.cast_one,one_mul] at h₁
  have h₂ := hsum 2 (by omega) (by omega)
  have h₃ := hsum 3 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at h₂ h₃
  have hrep := halasz_weighted_cosine_repulsion P (fun p => 1/(p:ℝ))
    (fun p => u*Real.log (p:ℝ)) (fun p _ => by positivity) K h₁ h₂ h₃
  have hsub : P ⊆ primesUpTo X := by
    intro p hp
    have hh : p ∈ sievePrimesUpTo (X:ℝ) := (mem_sdiff.mp hp).1
    rwa [mrt_sievePrimesUpTo_nat] at hh
  have hfull : (∑ p ∈ P, (1/(p:ℝ))*(1-|Real.cos (u*Real.log (p:ℝ)/2)|)) ≤
      ∑ p ∈ primesUpTo X, (1-|Real.cos (u*Real.log (p:ℝ)/2)|)/(p:ℝ) := by
    have hh := sum_le_sum_of_subset_of_nonneg
      (f := fun p : ℕ => (1/(p:ℝ))*(1-|Real.cos (u*Real.log (p:ℝ)/2)|))
      hsub (fun p _ _ => mul_nonneg (by positivity)
        (sub_nonneg.mpr (Real.abs_cos_le_one _)))
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
  apply le_trans _ hfull
  dsimp only [Function.comp_def] at hlarge
  have hll0 : 0 ≤ Real.log (Real.log (X:ℝ)) := Real.log_nonneg hL
  linarith only [hs,hrep,hlarge,hll0]

end TwoPointCorrelations

end OAI
