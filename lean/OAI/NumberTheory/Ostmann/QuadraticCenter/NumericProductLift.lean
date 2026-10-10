import OAI.NumberTheory.Ostmann.QuadraticCenter.LiftCountingBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericWitnessLift
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisor
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductTransform

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

def quadraticLiftMultiplierBound (Z : ℕ) : ℕ := ⌈(Z:ℝ)^(13/100:ℝ)⌉₊
def quadraticLiftHeight (X : ℝ) (Z : ℕ) : ℕ := ⌈X*(Z:ℝ)^(13/100:ℝ)⌉₊

theorem primeProductCenter_dvd (q : ℕ) (t : ℕ → ℤ) (p : ℕ)
    (hp : p ∈ q.primeFactors) :
    (p:ℤ) ∣ (primeProductCenter q t:ℤ)-t p :=
  primeBlockCenter_dvd q.primeFactors (fun _p hp => (Nat.mem_primeFactors.mp hp).1) t p hp

theorem eventually_divisor_quadratic_bounded_lift :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      2 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → 1 ≤ L → (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (s v d q : ℕ),
      1 ≤ s → s ≤ L^4 → v ∈ L.divisors → d ∈ L.divisors → 0 < q →
      ∀ X : ℝ,0 < X → (Z:ℝ)^10 ≤ (q:ℝ)/X → (q:ℝ)/X ≤ (Z:ℝ)^13 →
      ∀ (h : ℤ) (t : ℕ → ℤ),
      Real.sqrt ((2:ℝ)^d.primeFactors.card)*Real.exp (-(auxiliaryK Z z:ℝ)) ≤
        ‖divisorQuadraticSumP d A (mInv d) s v 1 ((q:ℝ)/X) h
          ((primeProductCenter q t:ℝ)/(q:ℝ))‖ →
      ∃ a : ℕ,1 ≤ a ∧ a ≤ quadraticLiftMultiplierBound Z ∧
        (boundedSubsetLifts q.primeFactors a t (quadraticLiftHeight X Z)).Nonempty := by
  filter_upwards [eventually_centered_quadratic_small_integer_witness (1/100) (by norm_num)] with T hT
  intro Z z L hZ hZl hZu hz hzl hzu hL hL1 hLZ A mInv s v d q hs hsL hv hd hq
    X hX hRlo hRhi h t hlarge
  let : ∀ p : d.primeFactors,NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  let : NeZero (∏ p : d.primeFactors,p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  have hdsq : Squarefree d := hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hprod : (∏ p : d.primeFactors,p.val) = d := divisor_coordinates_product hdsq
  have hl : Real.sqrt ((2:ℝ)^Fintype.card d.primeFactors)*Real.exp (-(auxiliaryK Z z:ℝ)) ≤
      ‖centeredQuadraticSum (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
        (fun p => A p.val) (mInv d:ZMod (∏ p : d.primeFactors,p.val)) s v 1 ((q:ℝ)/X) h
          ((((primeProductCenter q t:ℕ):ℤ):ℝ)/(q:ℝ))‖ := by
    simpa only [Fintype.card_coe,divisorQuadraticSumP,Int.cast_natCast] using hlarge
  obtain ⟨a,n,ha,haZ,hn,hinc⟩ := hT Z z L hZ hZl hZu hz hzl hzu hL1 hLZ
    d.primeFactors (fun p => p.val) (divisor_coordinate_prime d) (divisor_coordinates_coprime d)
    (fun p => A p.val) (mInv d:ZMod (∏ p : d.primeFactors,p.val)) s v q hs
    (Nat.pos_of_mem_divisors hv) hq hsL (Nat.dvd_of_mem_divisors hv)
    (by rw [hprod]; exact Nat.dvd_of_mem_divisors hd) X hX hRlo hRhi h (primeProductCenter q t) hl
  norm_num at haZ hn
  have hacap : a ≤ quadraticLiftMultiplierBound Z := by
    apply Nat.cast_le.mp (haZ.trans (Nat.le_ceil _))
  have hncap : |(n:ℝ)| ≤ (quadraticLiftHeight X Z:ℝ) := hn.trans (Nat.le_ceil _)
  refine ⟨a,ha,hacap,n,mem_boundedSubsetLifts.mpr ⟨?_,?_,?_⟩⟩
  · exact_mod_cast (abs_le.mp hncap).1
  · exact_mod_cast (abs_le.mp hncap).2
  · intro p hp
    exact hinc p (t p) (by exact_mod_cast (Nat.mem_primeFactors.mp hp).2.1)
      (primeProductCenter_dvd q t p hp)

end Ostmann.QuadraticCenter

end

end OAI
