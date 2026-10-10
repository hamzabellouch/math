import OAI.NumberTheory.Ostmann.Arithmetic.ContinuousPrimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPolynomialWeight

namespace OAI

/-! # Prime comparison for the actual clipped polynomial factors -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem ClippedPolynomialFactor.continuous_value (f : ClippedPolynomialFactor) :
    Continuous f.value := by
  have hp : LipschitzOnWith ⟨f.lip, f.lip_nonneg⟩ f.profile (Set.Icc f.lo f.hi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist (f.profile x) (f.profile y) ≤ f.lip * dist x y
    simpa only [dist_eq_norm, Real.norm_eq_abs] using f.lipschitz x hx y hy
  have hc : Continuous (fun x => clipRealInterval f.lo f.hi (f.polynomial.eval x)) :=
    continuous_const.max (continuous_const.min f.polynomial.continuous)
  apply continuousOn_univ.mp
  exact hp.continuousOn.comp hc.continuousOn
    (fun x _ => clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi)

theorem continuous_smoothPolynomialWeight {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    Continuous (smoothPolynomialWeight F) :=
  continuous_finsetProd _ (fun i _ => (F i).continuous_value)

/-- On one genuine polynomial root cell, the full smooth weight admits
prime-to-Page comparison with its explicit product variation budget. -/
theorem PublishedProgressionInput.smooth_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (hcode : rootCellCode S (Real.exp u) = rootCellCode S (Real.exp v)) :
    ‖complexPrimeInterval q a u v (fun y => smoothPolynomialWeight F (Real.exp y)) -
        ∫ y in Set.Ioc u v, smoothPolynomialWeight F (Real.exp y) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      smoothPolynomialBudget F *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) := by
  apply P.continuous_prime_comparison hQ hq hqQ ha u v hu huv hshort _
    ((continuous_smoothPolynomialWeight F).comp Real.continuous_exp).continuousOn
  intro s hs N hs0 hsN
  apply smoothPolynomialWeight_variation F S hroots (fun j => Real.exp (s j))
    (Real.exp_monotone.comp hs) N
  have hlo : Real.exp u ≤ Real.exp (s (N - 1)) := by
    rw [← hs0]
    exact Real.exp_le_exp.mpr (hs (Nat.zero_le _))
  have hhi : Real.exp (s (N - 1)) ≤ Real.exp v := by
    rw [← hsN]
    exact Real.exp_le_exp.mpr (hs (Nat.sub_le _ _))
  rw [hs0]
  exact (rootCellCode_convex S hlo hhi hcode).symm

end Ostmann

end OAI
