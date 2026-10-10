import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeBudgets
import OAI.Geometry.SurfaceImmersion.Geometry.CorrectedNormalSeed
import OAI.Geometry.SurfaceImmersion.Correction.UniformNormalizedMean

namespace OAI

/-! Polynomial control of the actual supported free-mode and normalized
mean constants, including their finite derivative-loss recurrences. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem freeModeBudget_polynomial (n L : ℕ) (B D : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => freeModeBudget n L (fun r => B r x) (fun r => D r x) q m) := by
  let κ := fun r x => max (errorConstant r (B r x))
    (D r x * initialConstant n (r+L) (B (r+L) x))
  let κ₀ := fun r x => max (fullErrorConstant n r (B r x))
    (D r x * initialConstant n (r+L) (B (r+L) x))
  have hκ (r : ℕ) : HasPolynomialBound (κ r) :=
    ((errorConstant_polynomial r).comp (hB r) (hB1 r)).max
      ((hD r).mul ((initialConstant_polynomial n (r+L)).comp (hB (r+L)) (hB1 (r+L))))
  have hκ₀ (r : ℕ) : HasPolynomialBound (κ₀ r) :=
    ((fullErrorConstant_polynomial n r).comp (hB r) (hB1 r)).max
      ((hD r).mul ((initialConstant_polynomial n (r+L)).comp (hB (r+L)) (hB1 (r+L))))
  have hi := (initialConstant_polynomial n m).comp (hB m) (hB1 m)
  have hsum := HasPolynomialBound.sum (Finset.range q)
    (fun i x => initialConstant n m (B m x)*
      FiniteParametrix.boundProfile (L+1) (fun r => κ r x) (fun r => κ₀ r x) i (m+(L+1)))
    (fun i _ => hi.mul (FiniteParametrix.boundProfile_polynomial (L+1) κ κ₀ hκ hκ₀ i (m+(L+1))))
  exact hsum.add ((amplitudeConstant_polynomial n m).comp (hB m) (hB1 m))

theorem freeMeanBudget_polynomial (n L : ℕ) (B D : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => freeMeanBudget n L (fun r => B r x) (fun r => D r x) q m) := by
  have hA := freeModeBudget_polynomial n L B D hB hD hB1 q (m+1)
  have h2A := (polynomialBound_const (show (0 : ℝ) ≤ 2 by norm_num)).mul hA
  have h1 := (polynomialBound_const zero_le_one).add h2A
  have h2 := (polynomialBound_const (show (0 : ℝ) ≤ 2 by norm_num)).add h2A
  exact ((polynomialBound_const (Nat.cast_nonneg n)).mul
    (polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity))).mul ((h1.mul h2).add h1)

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.RealModes
open SmallModes

theorem correctedSeedBudget_polynomial (L : ℕ) (B D : ℕ → ℝ → ℝ) (N : ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hN : HasPolynomialBound N) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => correctedSeedBudget L (fun r => B r x) (fun r => D r x) q m (N x)) := by
  exact ((polynomialBound_const zero_le_one).add
    (freeModeBudget_polynomial 4 L B D hB hD hB1 q m)).mul
      (((polynomialBound_const (Real.sqrt_nonneg 2)).mul
        (polynomialBound_const (show (0 : ℝ) ≤ 2^(m+(q+1)*(L+1)) by positivity))).mul hN)

theorem normalizedMeanBudget_polynomial (L : ℕ) (B D : ℕ → ℝ → ℝ) (N : ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hN : HasPolynomialBound N) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => normalizedMeanBudget L (fun r => B r x) (fun r => D r x) q m (N x)) := by
  exact (freeMeanBudget_polynomial 4 L B D hB hD hB1 q m).mul
    ((((polynomialBound_const (Real.sqrt_nonneg 2)).mul
      (polynomialBound_const (show (0 : ℝ) ≤ 2^(m+1+(q+1)*(L+1)) by positivity))).mul hN).pow 2)

end ClosedSurfaceR4.RealModes

end

end OAI
