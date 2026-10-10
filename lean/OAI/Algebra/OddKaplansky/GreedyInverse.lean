import OAI.Algebra.OddKaplansky.GreedyRing

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.GreedyRing
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {T : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommGroup T] [Fintype T] [Fintype S] [LinearOrder S]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hT : ∀ t : T, t^p=1)
variable (j : T →* Multiplicative (Fin 3 → ZMod p)) (hj : Function.Injective j)
variable (E : Matrix S S (MonoidAlgebra K T)) (hE : E*E=E)
include hT hj in

lemma prescribed_inverse_formula :
    (Q LocalAlgebra.augment.toRingHom E hE)⁻¹ =
      FiniteMatrixInverse.series
        (LocalAlgebra.scalarInverse (Q LocalAlgebra.augment.toRingHom E hE) *
          (Q LocalAlgebra.augment.toRingHom E hE-LocalAlgebra.scalarMatrix (Q LocalAlgebra.augment.toRingHom E hE)))
        (3*(p-1)+1)*LocalAlgebra.scalarInverse (Q LocalAlgebra.augment.toRingHom E hE) := by
  apply LocalAlgebra.matrix_inverse_formula p hT j hj
  change ((Q LocalAlgebra.augment.toRingHom E hE).map LocalAlgebra.augment.toRingHom).det≠0
  rw [Q_map]
  exact GreedyLift.matrix_det _ _
end
end OddKaplansky.GreedyRing

end

end OAI
