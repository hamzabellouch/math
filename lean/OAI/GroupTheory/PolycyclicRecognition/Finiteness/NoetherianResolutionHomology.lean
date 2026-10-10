import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.FiniteType
import Mathlib.GroupTheory.Finiteness

namespace OAI

/-! # Finite homology over an abelian quotient group ring

This is the noetherian algebra step for a finite projective resolution after
taking normal-subgroup coinvariants. The chain-level comparison is separate.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra

theorem integralAbelianGroupRing_noetherian (Q : Type) [CommGroup Q] [Group.FG Q] :
    IsNoetherianRing ℤ[Q] :=
  Algebra.FiniteType.isNoetherianRing ℤ ℤ[Q]

theorem module_finite_shortComplex_homology {R : Type} [CommRing R] [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat R)) [Module.Finite R S.X₂] :
    Module.Finite R S.homology := by
  let : Module.Finite R S.g.hom.ker := inferInstance
  let : Module.Finite R (S.g.hom.ker ⧸ S.moduleCatToCycles.range) := inferInstance
  let : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R (S.g.hom.ker ⧸ S.moduleCatToCycles.range)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

theorem integralAbelianGroupRing_finite_homology (Q : Type) [CommGroup Q] [Group.FG Q]
    (S : ShortComplex (ModuleCat ℤ[Q])) [Module.Finite ℤ[Q] S.X₂] :
    Module.Finite ℤ[Q] S.homology := by
  let := integralAbelianGroupRing_noetherian Q
  exact module_finite_shortComplex_homology S

end PolycyclicRecognition

end

end OAI
