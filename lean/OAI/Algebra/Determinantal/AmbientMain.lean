import OAI.Algebra.Determinantal.AmbientPersistence
import OAI.Algebra.Determinantal.AmbientCoefficient
import OAI.Algebra.Determinantal.AmbientNumerical

namespace OAI

open MvPolynomial
open PermanentBorder.PolarAnalysis PermanentBorder.KernelBilinear
namespace PermanentBorder

/-- Selected distinct simple ambient polar zeros of an affine determinant limit are
bounded by its mixed coefficient, the corresponding binomial count, and a numerical
matrix-size bound. The affine map and the ambient directions are arbitrary. -/
theorem ambient_polar_bound
    (N n K D : ℕ) (_hN : 0 < N) (_hD : 0 < D)
    (P : Poly (Fin N)) (hb : HasBorderDeterminant n P)
    (b : Fin N → ℂ)
    (L : (Option (Fin K) → ℂ) →L[ℂ] (Fin N → ℂ))
    (h : Fin K → Fin N → ℂ)
    (x : Fin D → ℂ × (Fin K → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => eval y P)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => eval y P)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    D ≤ ((X (0 : Fin 3) + X 1)^n * (X 0 + X 2)^(n-1) *
        (X 1 + X 2)^K : MvPolynomial (Fin 3) ℕ).coeff
      (Finsupp.single 0 (K+1) + Finsupp.single 1 (n-1) + Finsupp.single 2 (n-1)) ∧
    ((X (0 : Fin 3) + X 1)^n * (X 0 + X 2)^(n-1) *
        (X 1 + X 2)^K : MvPolynomial (Fin 3) ℕ).coeff
      (Finsupp.single 0 (K+1) + Finsupp.single 1 (n-1) + Finsupp.single 2 (n-1)) ≤ 2^K * (2*n-1).choose (K+1) ∧
    ((K+1 : ℕ) : ℝ) / (4 * Real.exp 1) *
      Real.rpow (D : ℝ) (1 / ((K+1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
  classical
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hb.1)
  | succ n =>
    have hrename := AmbientPolar.literal_coefficient_eq K n
    have hfirst := AmbientPolar.border_polar_mixed_count hb b L h x hx hz hs
    have hsecond := KernelBilinear.mixed_coefficient_bound (κ := Fin K) (n := n)
    have hcount : D ≤ 2^K * (2*(n+1)-1).choose (K+1) := by
      have hc := hfirst.trans hsecond
      simpa only [Fintype.card_fin, show 2*(n+1)-1 = 2*n+1 by omega] using hc
    refine ⟨?_, ?_, Polar.ambient_count_numerical_bound (n+1) K D hcount⟩
    · simpa only [Nat.add_sub_cancel, Fintype.card_fin, ← hrename] using hfirst
    · simpa only [Nat.add_sub_cancel, Fintype.card_fin, ← hrename,
        show 2*(n+1)-1 = 2*n+1 by omega] using hsecond

end PermanentBorder

end OAI
