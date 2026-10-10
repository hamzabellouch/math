import Mathlib

namespace OAI

namespace FiberFunctorProof
open CategoryTheory
universe u v
variable (k : Type u) [Field k]

 

theorem rep_leftRegular_projective (G : Type v) [Group G] :
    Projective (Rep.leftRegular k G) := by
  let e := Representation.ofMulActionSelfAsModuleEquiv (k := k) (G := G)
  let b := (Module.Basis.singleton (PUnit.{1}) (MonoidAlgebra k G)).map e.symm
  exact (Rep.toModuleMonoidAlgebra (k := k) (G := G)).projective_of_map_projective
    (P := Rep.leftRegular k G) (ModuleCat.projective_of_free b)

theorem fdrep_leftRegular_projective (G : Type) [Group G] [Fintype G] :
    Projective (FDRep.of (Representation.leftRegular k G)) := by
  apply (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective
  exact rep_leftRegular_projective k G
end FiberFunctorProof

end OAI
