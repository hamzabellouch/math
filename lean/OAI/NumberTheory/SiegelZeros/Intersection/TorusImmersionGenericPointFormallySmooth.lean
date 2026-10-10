import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.EntireFunctions.LogarithmicForm

namespace OAI

namespace SiegelZeros

section
open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets.Geometry

theorem torus_immersion_genericPoint_formallySmooth
    {X : Scheme} [IsIntegral X]
    (j : X ⟶ Spec (.of (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ)))) [IsImmersion j] :
    ((j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ))))).stalkMap
        (genericPoint X)).hom.FormallySmooth := by
  have : Algebra.FiniteType ℂ (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ)) :=
    WeightedTorusJets.laurent_finiteType
  let b := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin 4 →₀ ℤ))))
  have : LocallyOfFiniteType b :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact (j ≫ b).genericPoint_mem_smoothLocus_of_perfectField

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
