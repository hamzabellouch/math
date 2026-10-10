import OAI.Combinatorics.PolynomialVacuum.Algebra.CyclicBounds
import OAI.Combinatorics.PolynomialVacuum.Algebra.CyclicCups

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 

theorem cyclicity_of_cups {n : ℕ} (Ψ : State (n+4)) (ψ : State (n+2))
    (hex : LowerExchange (liftState Ψ) (n+4))
    (hc : ∀ i≤n+2, CupAt (liftState Ψ) (liftState ψ) (n+2) i)
    (hcy : NaturalCyclic (n+1) (liftState ψ))
    (hd : ∀ s i, (Ψ s).degreeOf i ≤ n+3)
    (hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i ≤ n+2)
    (hz : MinusZero Ψ) : NaturalCyclic (n+3) (liftState Ψ) := by
  have he : ∀ s, cyclicDiscrepancy Ψ s=0 := by
    apply cup_vanishing_rigidity (m:=n+3) (by omega) _ (cyclicDiscrepancy_exchange Ψ hex)
    · exact cyclicDiscrepancy_cup Ψ ψ hc hcy
    · intro s j hj; exact cyclicDiscrepancy_degree Ψ _ hd s j hj
    · intro s j hj hs; exact cyclicDiscrepancy_plus_degree Ψ _ hp s j hj hs
    · intro s j hj hs; exact cyclicDiscrepancy_minus_zero Ψ hz s j hj hs
  intro X
  apply sub_eq_zero.mp
  rw [← eval_cyclicDiscrepancy]
  funext s
  simp only [evalNatPolyTensor,he,map_zero,Pi.zero_apply]

end PolynomialVacuumAlgebra

end OAI
