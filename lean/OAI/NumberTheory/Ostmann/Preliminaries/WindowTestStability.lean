import OAI.NumberTheory.Ostmann.Preliminaries.DensityStability
import OAI.NumberTheory.Ostmann.Preliminaries.Sizes
import OAI.NumberTheory.Ostmann.Preliminaries.WindowAverages

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Filter
open scoped BigOperators

theorem eventually_upperWindow_A_test_stability (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ f : (p : PrimeUpTo (collisionScale 4 X)) → ZMod p.val → ℂ,
      (∀ p, ∑ r, ‖f p r‖ ^ 2 ≤ p.val) →
      (∑ p : PrimeUpTo (collisionScale 4 X), (Real.log p.val / p.val) *
        ‖((∑ n ∈ upperWindow d.A X, f p (n : ZMod p.val)) / ((upperWindow d.A X).card : ℂ)) -
          ((∑ r ∈ d.residueSupport p.val, f p r) / ((d.residueSupport p.val).card : ℂ))‖ ^ 2) ≤
        collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_upperWindow_collision d] with X hX
  intro f hf
  have h := weighted_A_test_error_le d (collisionScale 4 X)
    (fun i : upperWindow d.A X => i.val) (uniformWindowMass d.A X)
    (fun i : upperWindow d.B X => i.val) (uniformWindowMass d.B X) f hf
  have hb := h.trans hX.2.2
  have hav (p : PrimeUpTo (collisionScale 4 X)) :
      (∑ i : upperWindow d.A X, (uniformWindowMass d.A X i : ℂ) *
        f p (i.val : ZMod p.val)) =
      (∑ n ∈ upperWindow d.A X, f p (n : ZMod p.val)) /
        ((upperWindow d.A X).card : ℂ) :=
    uniformWindow_complex_average d.A X (fun n => f p (n : ZMod p.val))
  simpa only [hav, uniformMass_complex_average] using hb

theorem eventually_upperWindow_neg_B_test_stability (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ f : (p : PrimeUpTo (collisionScale 4 X)) → ZMod p.val → ℂ,
      (∀ p, ∑ r, ‖f p r‖ ^ 2 ≤ p.val) →
      (∑ p : PrimeUpTo (collisionScale 4 X), (Real.log p.val / p.val) *
        ‖((∑ n ∈ upperWindow d.B X, f p (-(n : ZMod p.val))) / ((upperWindow d.B X).card : ℂ)) -
          ((∑ r ∈ (d.residueSupport p.val)ᶜ, f p r) / (((d.residueSupport p.val)ᶜ).card : ℂ))‖ ^ 2) ≤
        collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_upperWindow_collision d] with X hX
  intro f hf
  have h := weighted_neg_B_test_error_le d (collisionScale 4 X)
    (fun i : upperWindow d.A X => i.val) (uniformWindowMass d.A X)
    (fun i : upperWindow d.B X => i.val) (uniformWindowMass d.B X) f hf
  have hb := h.trans hX.2.2
  have hav (p : PrimeUpTo (collisionScale 4 X)) :
      (∑ i : upperWindow d.B X, (uniformWindowMass d.B X i : ℂ) *
        f p (-(i.val : ZMod p.val))) =
      (∑ n ∈ upperWindow d.B X, f p (-(n : ZMod p.val))) /
        ((upperWindow d.B X).card : ℂ) :=
    uniformWindow_complex_average d.B X (fun n => f p (-(n : ZMod p.val)))
  simpa only [hav, uniformMass_complex_average] using hb

theorem eventually_upperWindow_density_stability (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p : PrimeUpTo (collisionScale 4 X), (Real.log p.val / p.val) *
        (d.residueDensity p.val - 1 / 2) ^ 2) ≤
        (collisionConstant 4 / 16) * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_upperWindow_collision d] with X hX
  have h := weighted_density_deviation_le d (collisionScale 4 X)
    (fun i : upperWindow d.A X => i.val) (uniformWindowMass d.A X)
    (fun i : upperWindow d.B X => i.val) (uniformWindowMass d.B X)
  apply h.trans
  have hb := div_le_div_of_nonneg_right hX.2.2 (by norm_num : (0 : ℝ) ≤ 16)
  simpa only [upperWindowCollision, div_mul_eq_mul_div] using hb

end Ostmann.Preliminaries

end OAI
