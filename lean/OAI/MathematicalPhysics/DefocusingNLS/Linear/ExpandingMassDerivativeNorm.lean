import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMassDerivativeEnergy

namespace OAI

/-! # Strong convergence from physical mass and the top derivative components -/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

theorem expandingMassDerivative_norm_bound (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L) (f : FourierL2) :
    ‖f‖ ^ 2 ≤ ((2 : ℝ) ^ N + 1) *
      (‖expandingPhysicalMassVector a N L ha ha1 hN hL f‖ ^ 2 +
        ∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a L N hL j f‖ ^ 2) := by
  have hf : HasSum (fun n : frequencyLattice => ‖f n‖ ^ 2) (‖f‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) f
  have hm : HasSum (fun n : frequencyLattice =>
      ‖expandingPhysicalMassVector a N L ha ha1 hN hL f n‖ ^ 2)
      (‖expandingPhysicalMassVector a N L ha ha1 hN hL f‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (by norm_num) (expandingPhysicalMassVector a N L ha ha1 hN hL f)
  have hd (j : Fin N → Fin 12) : HasSum (fun n : frequencyLattice =>
      ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2)
      (‖expandingOrderedFourierEnergy a L N hL j f‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (by norm_num) (expandingOrderedFourierEnergy a L N hL j f)
  have hs := (hm.add (hasSum_sum (s := Finset.univ) (fun j _ => hd j))).mul_left ((2 : ℝ) ^ N + 1)
  exact hasSum_le (expandingMassDerivative_coordinate_bound a L N ha ha1 hN hL f) hf hs

theorem tendsto_expanding_of_mass_derivatives_zero (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (f : ℕ → FourierL2)
    (hm : Tendsto (fun n => ‖expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n) (f n)‖)
      atTop (𝓝 0))
    (hd : ∀ j : Fin N → Fin 12, Tendsto
      (fun n => ‖expandingOrderedFourierEnergy a (L n) N (hL n) j (f n)‖) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hs := tendsto_finsetSum Finset.univ (fun j _ => (hd j).pow 2)
  have hu : Tendsto (fun n => ((2 : ℝ) ^ N + 1) *
      (‖expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n) (f n)‖ ^ 2 +
        ∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a (L n) N (hL n) j (f n)‖ ^ 2))
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, add_zero, mul_zero]
      using ((hm.pow 2).add hs).const_mul ((2 : ℝ) ^ N + 1)
  have hsq := squeeze_zero (fun n => sq_nonneg ‖f n‖)
    (fun n => expandingMassDerivative_norm_bound a (L n) N ha ha1 hN (hL n) (f n)) hu
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

end DefocusingNLS

end OAI
