import OAI.Algebra.OddKaplansky.PrescribedGreedy

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.OrderedSourceSector
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedSectorOrbit
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
variable (r : Rep (H := SectorStabilizer.H M p) M)
def stabilizerPoint : T M r →* SectorStabilizer.Point p :=
  RegularWreathProduct.rightHom.comp (T M r).subtype
lemma stabilizerPoint_injective : Function.Injective (stabilizerPoint M p r) := by
  change Function.Injective (RegularWreathProduct.rightHom.comp (T M r).subtype)
  rw [T_leftFixed]
  exact SectorStabilizer.toPoint_injective M p (fun x => (lmb M r x).toAdd) (lmb_weight M r)
local instance : CommGroup (T M r) :=
  { (inferInstance : Group (T M r)) with mul_comm := stabilizer_comm M p r }
variable {K : Type portUniverse1} [Field K] [CharP K p]

lemma augmentation_bound :
    RingHom.ker (LocalAlgebra.augment (K := K) (T := T M r)).toRingHom ^(3*(p-1)+1)=0 :=
  LocalAlgebra.kernel_nil_three p (stabilizer_exp M p r)
    (stabilizerPoint M p r) (stabilizerPoint_injective M p r)
variable {S : Type portUniverse2} [Fintype S] [LinearOrder S]
variable (E : Matrix S S (MonoidAlgebra K (T M r)))
variable (hE : E*E=E)
lemma inverse_formula :
    (GreedyRing.Q LocalAlgebra.augment.toRingHom E hE)⁻¹ =
      FiniteMatrixInverse.series
        (LocalAlgebra.scalarInverse (GreedyRing.Q LocalAlgebra.augment.toRingHom E hE) *
          (GreedyRing.Q LocalAlgebra.augment.toRingHom E hE-LocalAlgebra.scalarMatrix (GreedyRing.Q LocalAlgebra.augment.toRingHom E hE)))
        (3*(p-1)+1)*LocalAlgebra.scalarInverse (GreedyRing.Q LocalAlgebra.augment.toRingHom E hE) :=
  GreedyRing.prescribed_inverse_formula p (stabilizer_exp M p r)
    (stabilizerPoint M p r) (stabilizerPoint_injective M p r) E hE
end
end OddKaplansky.OrderedSourceSector

end

end OAI
