import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz
import OAI.NumberTheory.Ostmann.Dirichlet.EntireJensen
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.PrimeCountAbel
import OAI.NumberTheory.Ostmann.Dirichlet.PrimeCountAbelDefinitions
import OAI.NumberTheory.Ostmann.Dirichlet.PrincipalHeightBound
import OAI.NumberTheory.Ostmann.Dirichlet.RectangleIntegration
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaCompactStrip
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaStrip
import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicUnits
import OAI.NumberTheory.Ostmann.Reuse.SiegelGap

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Arithmetic.PrimeProgression

theorem exists_harmonicProgression_error_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi : ℝ,
      L₀ ≤ lo → lo ≤ hi → hi - lo ≤ 1 → ∀ (N M : ℕ) (a : ZMod M),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < M → IsUnit a →
      (M : ℝ) ≤ Real.exp (d * lo ^ (1 / 3 : ℝ)) →
      |harmonicProgression N M a lo hi - harmonicIntegral M lo hi| ≤
        K * Real.exp (-d * lo ^ (1 / 3 : ℝ)) :=
  harmonic_estimate_units_of_count_estimate
    Erdos970.Erdos970Dependency.SiegelWalfisz.large_modulus_siegel_walfisz

theorem exists_harmonicProgression_int_error_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi : ℝ,
      L₀ ≤ lo → lo ≤ hi → hi - lo ≤ 1 → ∀ (N M : ℕ) (r : ℤ),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < M → IsCoprime r (M : ℤ) →
      (M : ℝ) ≤ Real.exp (d * lo ^ (1 / 3 : ℝ)) →
      |harmonicProgression N M (r : ZMod M) lo hi - harmonicIntegral M lo hi| ≤
        K * Real.exp (-d * lo ^ (1 / 3 : ℝ)) :=
  harmonic_estimate_of_count_estimate
    Erdos970.Erdos970Dependency.SiegelWalfisz.large_modulus_siegel_walfisz

end Ostmann.Arithmetic.PrimeProgression

end OAI
