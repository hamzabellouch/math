import Mathlib
import PrimeNumberTheoremAnd.Erdos970.HadamardSupport
import OAI.NumberTheory.Jacobsthal.Siegel.LogarithmicForm

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

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

end Erdos970

end OAI
