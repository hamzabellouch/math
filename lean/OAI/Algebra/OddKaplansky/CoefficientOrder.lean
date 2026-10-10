import OAI.Algebra.OddKaplansky.FiniteChoice

namespace OAI

section
namespace OddKaplansky.QuadraticTower
noncomputable section
open scoped Classical
variable (p : ℕ) [Fact p.Prime] (hp : p≠2)
def firstCoordinates : FirstField p hp ≃ₗ[ZMod p] (Fin 2 → ZMod p) :=
  ((basis (eta p hp)).basis.reindex (finCongr (basis_dim (eta p hp)))).equivFun
def secondCoordinates : CoeffField p hp ≃ₗ[FirstField p hp] (Fin 2 → FirstField p hp) :=
  ((basis (xi p hp)).basis.reindex (finCongr (basis_dim (xi p hp)))).equivFun

def coefficientTuple (z : CoeffField p hp) : Fin 4 → ZMod p :=
  ![firstCoordinates p hp (secondCoordinates p hp z 0) 0,
    firstCoordinates p hp (secondCoordinates p hp z 0) 1,
    firstCoordinates p hp (secondCoordinates p hp z 1) 0,
    firstCoordinates p hp (secondCoordinates p hp z 1) 1]
lemma coefficientTuple_injective : Function.Injective (coefficientTuple p hp) := by
  intro a b he
  apply (secondCoordinates p hp).injective
  funext i
  apply (firstCoordinates p hp).injective
  funext j
  fin_cases i <;> fin_cases j
  · exact congrFun he 0
  · exact congrFun he 1
  · exact congrFun he 2
  · exact congrFun he 3
@[instance_reducible]
def fieldOrder : LinearOrder (CoeffField p hp) :=
  @LinearOrder.lift' _ _ (@FiniteChoice.functionOrder (Fin 4) (ZMod p) inferInstance inferInstance (FiniteChoice.residueOrder p))
    (coefficientTuple p hp) (coefficientTuple_injective p hp)
end
end OddKaplansky.QuadraticTower

end

end OAI
