import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra
import OAI.Geometry.Immersion.ClosedSurface.MeanError
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedForcedSize

namespace OAI

/-! The finite free and forced parametrices have polynomial budgets. These
are the actual constants used by the existing mode estimates. -/
noncomputable section
namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem errorConstant_polynomial (m : ℕ) :
    HasPolynomialBound (errorConstant m) := by
  unfold errorConstant reducedConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem fullErrorConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (fullErrorConstant n m) := by
  unfold fullErrorConstant reducedConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem amplitudeConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (amplitudeConstant n m) := by
  unfold amplitudeConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem initialConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (initialConstant n m) := by
  unfold initialConstant
  exact ((polynomialBound_const (by positivity)).add
    ((polynomialBound_const (by positivity)).mul polynomialBound_id)).add
      (amplitudeConstant_polynomial n m)

theorem freeModeConstant_polynomial (n m q : ℕ) :
    HasPolynomialBound (fun x => freeModeConstant n m x q) := by
  induction q with
  | zero => exact amplitudeConstant_polynomial n m
  | succ q ih =>
    exact ih.add ((initialConstant_polynomial n m).mul
      ((fullErrorConstant_polynomial n (m+1+q)).pow (q+1)))

theorem gradientErrorConstant_polynomial (n m q : ℕ) :
    HasPolynomialBound (fun x => gradientErrorConstant n m x q) :=
  ((polynomialBound_const zero_le_one).add (freeModeConstant_polynomial n (m+1) q)).add
    (freeModeConstant_polynomial n m q)

theorem meanErrorConstant_polynomial (n m q : ℕ) :
    HasPolynomialBound (fun x => meanErrorConstant n m x q) := by
  unfold meanErrorConstant
  exact (((polynomialBound_const (Nat.cast_nonneg n)).mul
    (polynomialBound_const (by positivity))).mul
      (gradientErrorConstant_polynomial n m q)).mul
        ((polynomialBound_const (by positivity)).add (gradientErrorConstant_polynomial n m q))

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.FiniteParametrix
open RealModes

theorem boundProfile_polynomial (L : ℕ) (K C : ℕ → ℝ → ℝ)
    (hK : ∀ m, HasPolynomialBound (K m)) (hC : ∀ m, HasPolynomialBound (C m))
    (q m : ℕ) : HasPolynomialBound (fun x => boundProfile L (fun r => K r x) (fun r => C r x) q m) := by
  induction q generalizing m with
  | zero => exact hC m
  | succ q ih => exact (hK m).mul (ih (m+L))

end ClosedSurfaceR4.FiniteParametrix

namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem forcedModeBudget_polynomial (n L : ℕ) (B D : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => forcedModeBudget n L (fun r => B r x) (fun r => D r x) q m) := by
  let κ := fun r x => max (errorConstant r (B r x))
    (D r x * initialConstant n (r+L) (B (r+L) x))
  have hκ (r : ℕ) : HasPolynomialBound (κ r) :=
    ((errorConstant_polynomial r).comp (hB r) (hB1 r)).max
      ((hD r).mul ((initialConstant_polynomial n (r+L)).comp (hB (r+L)) (hB1 (r+L))))
  have hi := (initialConstant_polynomial n m).comp (hB m) (hB1 m)
  have hsum := HasPolynomialBound.sum (Finset.range q)
    (fun i x => initialConstant n m (B m x)*
      FiniteParametrix.boundProfile (L+1) (fun r => κ r x) (fun r => κ r x) i (m+(L+1)))
    (fun i _ => hi.mul (FiniteParametrix.boundProfile_polynomial (L+1) κ κ hκ hκ i (m+(L+1))))
  exact hi.add hsum

end ClosedSurfaceR4.SmallModes

end

end OAI
