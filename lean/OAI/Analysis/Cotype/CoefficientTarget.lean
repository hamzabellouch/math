import OAI.Analysis.Cotype.Damping
import OAI.Analysis.Cotype.Moments
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

noncomputable section
namespace Cotype

abbrev SignMatrix (m : ℕ) := (Fin m × Fin m) → Bool

def degreeCutoff (m : ℕ) : ℕ := ⌈2 * Real.logb 2 (m : ℝ)⌉₊

def ScalarAdmissible (m : ℕ) (a b : ℝ) (Ψ : SignMatrix m → ℝ)
    (f g : Cube m → ℝ) : Prop :=
  IsOdd Ψ ∧ IsOdd f ∧ IsOdd g ∧
  (∀ S, |Ψ S| ≤ 4) ∧ (∀ s, |f s| ≤ 4) ∧ (∀ t, |g t| ≤ 4) ∧
  (∀ i, fourier f (unitIndex i) = a) ∧ (∀ j, fourier g (unitIndex j) = b) ∧
  (∀ (i : Fin m) (S : SignMatrix m),
    average (fun σ : Cube m => sign (σ i) * Ψ (xorCube (rowCube σ) S)) =
      a * g (fun j => S (i,j))) ∧
  (∀ (j : Fin m) (S : SignMatrix m),
    average (fun τ : Cube m => sign (τ j) * Ψ (xorCube (columnCube τ) S)) =
      b * f (fun i => S (i,j)))

def CoefficientTarget : Prop := ∀ (m : ℕ) (a b : ℝ),
  4 ≤ degreeCutoff m → degreeCutoff m < m → 0 < a → 0 < b →
  80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤ min ((m : ℝ)*a) ((m : ℝ)*b) →
  ∃ c : ℝ, 0 < c ∧ ∀ (Ψ : SignMatrix m → ℝ) (f g : Cube m → ℝ),
    ScalarAdmissible m a b Ψ f g →
      ∃ P : SignMatrix m, 2 ≤ (binaryMatrix P).rank ∧ c ≤ |fourier Ψ P|

end Cotype

end

end OAI
