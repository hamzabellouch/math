import OAI.Geometry.SingularHomology.SingularSubdivisionSmallness
import OAI.Geometry.SingularHomology.SingularRealizedSmallness
import OAI.Geometry.SingularHomology.ActualSingularSubdivisionMap
import OAI.Geometry.SingularHomology.SingularSubdivisionIterateRealization

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SingularSmallChains

variable {X : Type} [TopologicalSpace X]

theorem actualSubdivision_eq_degreeOperator (n : ℕ) :
    ActualSingularSubdivision.subdivision n =
      SingularSubdivisionIterateRealization.degreeOperator n := by
  unfold ActualSingularSubdivision.subdivision ActualSingularSubdivision.subdivisionChain
  rw [ActualSingularSubdivision.realize_eq_aux]

theorem actualSubdivision_pow_generator (n k : ℕ) (σ : RealSingularSimplex X n) :
    (((End.of (ActualSingularSubdivision.chainMap.app (TopCat.of X)) ^ k).asHom).f n).hom
      (realSingularGenerator σ 1) =
    ((realSingularChainMap σ σ.continuous).f n).hom
      (SimplexSingularRealization.realize n n
        ((SingularSubdivision.subdivision (SingularSubdivision.simplexCenters n) (n + 1))^[k]
          (SingularSubdivision.generator (SingularSubdivision.standardVertices n)))) := by
  rw [end_pow_f_hom, ActualSingularSubdivision.chainMap_app_f,
    Module.End.pow_apply, actualSubdivision_eq_degreeOperator]
  exact SingularSubdivisionIterateRealization.iterate_simplexChain n k σ

theorem exists_actualSubdivision_pow_mem_range {I : Type}
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∀ (n : ℕ) (z : (realSingularChainComplex X).X n), ∃ k : ℕ,
      (((End.of (ActualSingularSubdivision.chainMap.app (TopCat.of X)) ^ k).asHom).f n).hom z ∈
        LinearMap.range ((inclusion U).f n).hom := by
  apply exists_pow_mem_range_inclusion_of_generators U ActualSingularSubdivision.chainMap
  intro n σ
  obtain ⟨N, hN⟩ := exists_iterated_realize_mem_range_inclusion U hopen hcover n σ
  refine ⟨N, ?_⟩
  rw [actualSubdivision_pow_generator]
  exact hN N le_rfl

end Problem340.SingularSmallChains

end

end OAI
