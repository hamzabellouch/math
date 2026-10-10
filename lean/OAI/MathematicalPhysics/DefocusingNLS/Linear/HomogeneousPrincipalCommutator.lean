import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCompactErrors
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPrincipalPotential

namespace OAI

/-! # The compact-error estimate with the actual physical principal potential

The principal action on each ordered derivative is exactly the same
pointwise odd-power derivative as in the Schrödinger linearization.
-/

open MeasureTheory
open scoped ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure E)

theorem homogeneousPrincipalPotential_decomposition (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a k ha ha1 hk q x‖ ^ (2 * (m + 1)) ≤ M)
    (f : H) :
    homogeneousPrincipalPotential (m + 1) (homogeneousPhysicalCLM a k ha ha1 hk q)
        (homogeneousPhysicalCLM a k ha ha1 hk q).continuous M hM hQB f =
      homogeneousPhysicalL2Product a k ha ha1 hk
        (homogeneousLinearizedFirstCoefficient a k ha ha1 hk m q) f +
      homogeneousPhysicalL2Product a k ha ha1 hk
        (homogeneousLinearizedSecondCoefficient a k ha ha1 hk m q) (star f) := by
  let A := homogeneousLinearizedFirstCoefficient a k ha ha1 hk m q
  let B := homogeneousLinearizedSecondCoefficient a k ha ha1 hk m q
  apply Lp.ext
  filter_upwards [homogeneousPrincipalAction_ae (m + 1)
      (homogeneousPhysicalCLM a k ha ha1 hk q)
      (homogeneousPhysicalCLM a k ha ha1 hk q).continuous M hM hQB f,
    homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk A f,
    homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk B (star f),
    Lp.coeFn_star f,
    Lp.coeFn_add (homogeneousPhysicalL2Product a k ha ha1 hk A f)
      (homogeneousPhysicalL2Product a k ha ha1 hk B (star f))] with x hp hA hB hs hadd
  change homogeneousPrincipalAction (m + 1) (homogeneousPhysicalCLM a k ha ha1 hk q)
    (homogeneousPhysicalCLM a k ha ha1 hk q).continuous M hM hQB f x = _
  rw [hp, hadd, Pi.add_apply]
  change _ = homogeneousPhysicalL2ProductValue a k ha ha1 hk A f x +
    homogeneousPhysicalL2ProductValue a k ha ha1 hk B (star f) x
  rw [hA, hB, hs, Pi.star_apply]
  simp only [A, B, homogeneousLinearizedFirstCoefficient, homogeneousLinearizedSecondCoefficient,
    map_smul, ZeroAtInftyContinuousMap.smul_apply, homogeneousYProduct_physical,
    homogeneousOddPower_physical, homogeneousConjugation_physical, smul_eq_mul,
    oddPowerDerivative, oddPowerNonlinearity, add_apply, smul_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply, starL'_apply, starRingEnd_apply, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem homogeneousLinearized_derivative_commutator (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (m : ℕ) (q u : HomogeneousY a ((N + 1 : ℕ) : ℝ))
    (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M) :
    homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j
        (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) -
      homogeneousPrincipalPotential (m + 1)
        (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q)
        (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q).continuous M hM hQB
        (homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j u) =
      homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u := by
  rw [homogeneousPrincipalPotential_decomposition,
    homogeneousLinearized_ordered_derivative]
  abel

theorem homogeneousLinearized_physical_compact_errors (a ε : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (hε : 0 < ε)
    (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : HomogeneousY a ((N + 1 : ℕ) : ℝ),
      ‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk
        (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u)‖ +
      Real.sqrt (∑ j : Fin (N + 1) → Fin 12,
        ‖homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j
            (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) -
          homogeneousPrincipalPotential (m + 1)
            (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q)
            (homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q).continuous M hM hQB
            (homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j u)‖ ^ 2) ≤
      ε * ‖u‖ + C * ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk u‖ := by
  simpa only [homogeneousLinearized_derivative_commutator] using
    homogeneousLinearized_compact_errors a ε N ha ha1 hk m q hε

end DefocusingNLS

end OAI
