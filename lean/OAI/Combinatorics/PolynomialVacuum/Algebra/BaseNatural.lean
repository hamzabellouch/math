import OAI.Combinatorics.PolynomialVacuum.Algebra.BasePolynomials
import OAI.Combinatorics.PolynomialVacuum.Algebra.FullCyclicity

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem baseThree_exchange_last (x y z : ℂ) (a b c : Spin) :
    (∑ ab : Pair, exchangeNumerator y z (b,c) ab * baseThree x y z a ab.1 ab.2)=
      exchangeDenominator y z * baseThree x z y a b c := by
  simp_rw [← baseThree_rotation y z x a,← baseThree_rotation z y x a]
  calc
    _ = zeta^charge a * ∑ ab : Pair, exchangeNumerator y z (b,c) ab * baseThree y z x ab.1 ab.2 a := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring
    _ = _ := by rw [baseThree_exchange]; ring

theorem vacuumTwo_exchange : LowerExchange (liftState vacuumTwo) 2 := by
  intro j hj X
  have : j=0 := by omega
  subst j
  funext s
  simpa [siteR,pairLinear,pairAction,replacePair,swapSite,Equiv.swap_apply_def,update_nat_decidable] using baseTwo_exchange (X 0) (X 1) (s 0) (s 1)

theorem vacuumThree_exchange : LowerExchange (liftState vacuumThree) 3 := by
  intro j hj X
  have : j=0 ∨ j=1 := by omega
  rcases this with rfl|rfl
  · funext s
    simpa [siteR,pairLinear,pairAction,replacePair,swapSite,Equiv.swap_apply_def,update_nat_decidable] using baseThree_exchange (X 0) (X 1) (X 2) (s 0) (s 1) (s 2)
  · funext s
    simpa [siteR,pairLinear,pairAction,replacePair,swapSite,Equiv.swap_apply_def,update_nat_decidable] using baseThree_exchange_last (X 0) (X 1) (X 2) (s 0) (s 1) (s 2)

theorem vacuumTwo_cyclic : NaturalCyclic 1 (liftState vacuumTwo) := by
  intro X
  funext s
  simp only [cyclicTransform,rotateTensor,lift_vacuumTwo,natRotate_zero,natRotate_succ]
  rw [← baseTwo_rotation (X 0) (X 1) (s 1) (s 0)]
  rw [← mul_assoc,← zpow_add₀ (by exact pow_ne_zero _ (pow_ne_zero _ q_ne_zero) : zeta≠0)]
  simp

theorem vacuumThree_cyclic : NaturalCyclic 2 (liftState vacuumThree) := by
  intro X
  funext s
  simp only [cyclicTransform,rotateTensor,lift_vacuumThree,natRotate_zero,natRotate_succ]
  rw [← baseThree_rotation (X 0) (X 1) (X 2) (s 2) (s 0) (s 1)]
  rw [← mul_assoc,← zpow_add₀ (by exact pow_ne_zero _ (pow_ne_zero _ q_ne_zero) : zeta≠0)]
  simp

theorem vacuumTwo_firstCup : FirstCupReduction (liftState vacuumTwo) (liftState vacuumZero) 0 := by
  intro X hX
  funext s
  simpa [naturalFusion,fusionProduct,cupLinear,fusionPair,skipTwo,hX] using baseTwo_cup (X 0) (s 0) (s 1)

theorem vacuumThree_firstCup : FirstCupReduction (liftState vacuumThree) (liftState vacuumOne) 1 := by
  intro X hX
  funext s
  simpa [naturalFusion,fusionProduct,cupLinear,fusionPair,skipTwo,hX,mul_assoc] using baseThree_cup (X 0) (X 2) (s 0) (s 1) (s 2)

end PolynomialVacuumAlgebra

end OAI
