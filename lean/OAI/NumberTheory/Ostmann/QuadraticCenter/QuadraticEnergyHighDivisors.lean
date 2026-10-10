import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyDivisors
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyHighCorrelation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology ComplexConjugate
open Filter

theorem divisorQuadraticSum_high_correlation_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L S d e : ℕ), Squarefree L → d ∣ L → e ∣ L →
      ∀ (u K : ℝ), 2 * L ^ 2 ≤ S → (S : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv mInv' : ℤ)
        (v : ℕ), 0 < v → ∀ (R h θ : ℝ), 0 < R →
      ‖∑ s ∈ quadraticHighWeightIndices S L u K, ((u ^ s.primeFactors.card : ℝ) : ℂ) *
        (divisorQuadraticSum d A mInv s v R h θ *
          conj (divisorQuadraticSum e A mInv' s v R h θ) / (s : ℂ))‖ ≤
        cutoffFourierBound ^ 2 * Real.exp (-10 * K) := by
  filter_upwards [centeredQuadraticSum_high_correlation_eventually] with T hT
  intro L S d e hL hd he u K hS hSupper hu huupper hK A mInv mInv' v hv R h θ hR
  have hdsq := hL.squarefree_of_dvd hd
  have hesq := hL.squarefree_of_dvd he
  have : NeZero L := ⟨hL.ne_zero⟩
  have : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  have : ∀ p : e.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime e p).ne_zero⟩
  have : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  have : NeZero (∏ p : e.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero e⟩
  exact hT (fun p : d.primeFactors => p.val) (fun p : e.primeFactors => p.val)
    (divisor_coordinate_prime d) (divisor_coordinate_prime e)
    (divisor_coordinates_coprime d) (divisor_coordinates_coprime e)
    (fun p => A p.val) (fun p => A p.val)
    (mInv : ZMod (∏ p : d.primeFactors, p.val)) (mInv' : ZMod (∏ p : e.primeFactors, p.val))
    S L (by simpa only [divisor_coordinates_product hdsq] using hd)
    (by simpa only [divisor_coordinates_product hesq] using he)
    u K hS hSupper hu huupper hK v hv R h θ hR

theorem squarefree_divisor_weight_sum {L : ℕ} (hL : Squarefree L) (lam : ℝ) :
    (∑ d ∈ L.divisors, lam ^ d.primeFactors.card) = (1 + lam) ^ L.primeFactors.card := by
  classical
  have hP : ∀ p ∈ L.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  rw [sum_squarefree_divisors_eq_cube hL]
  simp_rw [primeSubsetProduct_primeFactors_card hP]
  simpa only [one_pow, mul_one, Fintype.card_coe, add_comm] using
    Fintype.sum_pow_mul_eq_add_pow L.primeFactors lam (1 : ℝ)

end Ostmann.QuadraticCenter

end

end OAI
