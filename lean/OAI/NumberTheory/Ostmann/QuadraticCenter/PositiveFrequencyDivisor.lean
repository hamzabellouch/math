import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyArray
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyDivisors

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def divisorQuadraticSumP (d : ℕ) (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ)
    (s v P : ℕ) (R h θ : ℝ) : ℂ :=
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  letI : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  centeredQuadraticSum (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
    (fun p => A p.val) (mInv : ZMod (∏ p : d.primeFactors, p.val)) s v P R h θ

@[simp] theorem divisorQuadraticSumP_one (d : ℕ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (s v : ℕ) (R h θ : ℝ) :
    divisorQuadraticSumP d A mInv s v 1 R h θ =
      divisorQuadraticSum d A mInv s v R h θ := rfl

def positiveDivisorArray (L q : ℕ) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (P : ℕ) (R h θ : ℝ) (s : ℕ) : ℂ :=
  (Real.sqrt (s : ℝ) : ℂ)⁻¹ *
    ∑ v ∈ L.divisors, (jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ) *
      ∑ d ∈ L.divisors,
        (lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
          divisorQuadraticSumP d A (mInv d) s v P R h θ

end Ostmann.QuadraticCenter

end

end OAI
