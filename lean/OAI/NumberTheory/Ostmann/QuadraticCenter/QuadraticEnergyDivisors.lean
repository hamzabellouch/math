import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorGram
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelation

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem divisor_coordinate_prime (d : ℕ) (p : d.primeFactors) : Nat.Prime p.val :=
  (Nat.mem_primeFactors.mp p.property).1

theorem divisor_coordinates_coprime (d : ℕ) :
    Pairwise (fun p q : d.primeFactors => p.val.Coprime q.val) := by
  intro p q hpq
  exact (Nat.coprime_primes (divisor_coordinate_prime d p) (divisor_coordinate_prime d q)).mpr
    (fun h => hpq (Subtype.ext h))

theorem divisor_coordinates_product_ne_zero (d : ℕ) :
    (∏ p : d.primeFactors, p.val) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => (divisor_coordinate_prime d p).ne_zero)

theorem divisor_coordinates_product {d : ℕ} (hd : Squarefree d) :
    (∏ p : d.primeFactors, p.val) = d := by
  exact (Finset.prod_coe_sort d.primeFactors (fun p : ℕ => p)).trans
    (Nat.prod_primeFactors_of_squarefree hd)

def divisorQuadraticSum (d : ℕ) (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ)
    (s v : ℕ) (R h θ : ℝ) : ℂ :=
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  letI : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  centeredQuadraticSum (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
    (fun p => A p.val) (mInv : ZMod (∏ p : d.primeFactors, p.val)) s v 1 R h θ

theorem divisorQuadraticSum_dyadic_correlation {d e S v : ℕ}
    (hd : Squarefree d) (he : Squarefree e)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv mInv' : ℤ)
    (hS : 0 < S) (hv : 0 < v) {R : ℝ} (hR : 0 < R) (h θ : ℝ)
    (hperiod : (Nat.lcm d e : ℝ) * (harmonic (Nat.lcm d e) : ℝ) ≤ S) :
    ‖∑ s ∈ Finset.Ico S (2*S),
      divisorQuadraticSum d A mInv s v R h θ *
        conj (divisorQuadraticSum e A mInv' s v R h θ) / (s : ℂ)‖ ≤
      quadraticCorrelationConstant *
        ((Nat.gcd d e : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ))) := by
  have : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  have : ∀ p : e.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime e p).ne_zero⟩
  have : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  have : NeZero (∏ p : e.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero e⟩
  have hc := centeredQuadraticSum_dyadic_correlation
    (fun p : d.primeFactors => p.val) (fun p : e.primeFactors => p.val)
    (divisor_coordinate_prime d) (divisor_coordinate_prime e)
    (divisor_coordinates_coprime d) (divisor_coordinates_coprime e)
    (fun p => A p.val) (fun p => A p.val)
    (mInv : ZMod (∏ p : d.primeFactors, p.val))
    (mInv' : ZMod (∏ p : e.primeFactors, p.val)) hS hv hR h θ
    (by simpa only [divisor_coordinates_product hd, divisor_coordinates_product he] using hperiod)
  change ‖∑ s ∈ Finset.Ico S (2*S),
    divisorQuadraticSum d A mInv s v R h θ *
      conj (divisorQuadraticSum e A mInv' s v R h θ) / (s : ℂ)‖ ≤ _ at hc
  simpa only [divisor_coordinates_product hd, divisor_coordinates_product he] using hc

end Ostmann.QuadraticCenter

end

end OAI
