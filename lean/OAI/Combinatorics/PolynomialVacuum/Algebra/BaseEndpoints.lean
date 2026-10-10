import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseNatural
import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseThreeNode

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem baseThree_lastCup (x y : ℂ) (a b c : Spin) :
    baseThree x y (T*y) a b c =
      (1+T)*y * (x-t^5*y)*(x-t^6*y) * cup (b,c) * (if a=Spin.zero then 1 else 0) := by
  rw [← baseThree_rotation y (T*y) x a b c,baseThree_cup]
  cases a <;> simp [charge]

theorem vacuumThree_lastCup : CupAt (liftState vacuumThree) (liftState vacuumOne) 1 1 := by
  intro X hX
  funext s
  simpa [naturalFusion,fusionProduct,fusionPair,cupLinear,skipTwo,hX,mul_assoc] using baseThree_lastCup (X 0) (X 1) (s 0) (s 1) (s 2)

theorem vacuumTwo_nodes : NaturalCupNodes (liftState vacuumTwo) (liftState vacuumZero) 0 := by
  intro X i hi hX
  have : i=0 := by omega
  subst i
  rw [naturalPrescription_last_cup]
  exact vacuumTwo_firstCup X hX

theorem vacuumThree_nodes : NaturalCupNodes (liftState vacuumThree) (liftState vacuumOne) 1 := by
  intro X i hi hX
  interval_cases i
  · funext s
    simpa [naturalPrescription,leftFusion,braidTrain,cupLinear,siteR,pairLinear,pairAction,
      replacePair,skipTwo,skipOne,hX,update_nat_decidable,mul_assoc] using baseThree_node (X 0) (X 1) (s 0) (s 1) (s 2)
  · rw [naturalPrescription_last_cup]
    exact vacuumThree_lastCup X hX

theorem vacuumOne_lastZero : LastZeroReduction (liftState vacuumOne) (liftState vacuumZero) 0 := by
  intro X s hX hs
  simp [prefixProduct]

theorem vacuumTwo_lastZero : LastZeroReduction (liftState vacuumTwo) (liftState vacuumOne) 1 := by
  intro X s hX hs
  cases h0 : s 0 <;> cases h1 : s 1 <;>
    simp_all [baseTwo,prefixProduct]

theorem baseThree_lastZero (x y : ℂ) (a b c : Spin) (hc : c≠Spin.plus) :
    baseThree x y 0 a b c=(if c=Spin.zero then x*y*baseTwo x y a b else 0) := by
  cases a <;> cases b <;> cases c <;>
    simp_all [baseThree,baseThreeFactor,baseTwo]
  all_goals vacuum_ring_finish

theorem vacuumThree_lastZero : LastZeroReduction (liftState vacuumThree) (liftState vacuumTwo) 2 := by
  intro X s hX hs
  simpa [prefixProduct,hX,Finset.prod_range_succ] using baseThree_lastZero (X 0) (X 1) (s 0) (s 1) (s 2) hs

end PolynomialVacuumAlgebra

end OAI
