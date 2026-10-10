import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleKernelRegroup
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductHeight

namespace OAI

/-! The actual regrouped kernel on the full Mellin line. No product
cutoff or Mellin-frequency remainder is discarded by these identities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev largeTupleSelectedSupport {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullSquarefreePrimeSupport 2
    (fun a : s => largeTupleCoordinateWeight ξ X k a)
    (fun a : s => largeTupleNormScale k a) 1

abbrev largeTupleOtherSupport {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullSquarefreePrimeSupport 2
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a) 1

abbrev largeTupleSelectedCoefficient {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullPrimeCoefficient 2
    (fun a : s => largeTupleCoordinateWeight ξ X k a)
    (fun a : s => largeTupleNormScale k a)

abbrev largeTupleOtherCoefficient {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullPrimeCoefficient 2
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a)

def largeTupleSmoothedPolynomial {i j : ℕ} (ℓ : ℤ) (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) (u : ℝ) : ℂ :=
  centeredProductSmoothed (largeTupleSelectedSupport ξ X k s)
    (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
    (largeTupleOtherCoefficient ξ X k s) ℓ primeProductEnvelope X u

theorem largeTupleRegroupedKernel_low_integral {i j : ℕ} (ℓ : ℤ) (ξ X : ℝ)
    (Ct : ℕ) {H : ℝ} (hH : 0 < H) (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleRegroupedKernel i j ℓ ξ Ct H X k s =
      ∫ t : ℝ, (lowHeightWeight H ((1+Real.log X)^Ct) t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
          largeTupleSmoothedPolynomial ℓ ξ X k s t := by
  exact centered_product_low_integral (largeTupleSelectedSupport ξ X k s)
    (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
    (largeTupleOtherCoefficient ξ X k s) ℓ primeProductEnvelope X X
    ((1+Real.log X)^Ct) hH

theorem largeTupleSmoothedPolynomial_mellin {i j : ℕ} (ℓ : ℤ) (ξ : ℝ)
    {X : ℝ} (hX : 0 < X) (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) (u : ℝ) :
    largeTupleSmoothedPolynomial ℓ ξ X k s u =
      ∫ τ : ℝ, zeroLineMellinWeight primeProductEnvelope X τ*
        centeredProductPolynomial (largeTupleSelectedSupport ξ X k s)
          (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
          (largeTupleOtherCoefficient ξ X k s) ℓ (u-τ) := by
  exact centered_product_mellin (largeTupleSelectedSupport ξ X k s)
    (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
    (largeTupleOtherCoefficient ξ X k s)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    ℓ primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX u


end CubicFirstMoment

end

end OAI
