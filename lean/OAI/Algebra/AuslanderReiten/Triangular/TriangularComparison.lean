import OAI.Algebra.AuslanderReiten.Triangular.TriangularCrossHom
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomMap
import OAI.Algebra.AuslanderReiten.Cones.ConeComparison

namespace OAI

noncomputable section
namespace ArExplicit.TriangularInduction
open CategoryTheory CochainComplex.HomComplex
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

@[simp] theorem crossCohomologyEquiv_mk
    (x : Cocycle P (tensorCochain (k := k) (F := F) P) n) :
    crossCohomologyEquiv P P n (CohomologyClass.mk x) =
      CohomologyClass.mk ((crossFullHomEquivalence P P).cocycle n x) := rfl

theorem crossCohomology_postcomp (x : CohomologyClass P P n) :
    crossCohomologyEquiv P P n (fullHomPostcomp v n x) =
      fullHomPostcomp (crossChainMap v) n (mapFullHom (jFunctor k R F) P P n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPostcomp_mk, crossCohomologyEquiv_mk, mapFullHom_mk, fullHomPostcomp_mk]
  congr 1
  apply Cocycle.ext
  change crossCochainEquiv P P n (x.1.comp (Cochain.ofHom v) (add_zero n)) =
    (x.1.map (jFunctor k R F)).comp (Cochain.ofHom (crossChainMap v)) (add_zero n)
  apply Cochain.ext
  intro i j hij
  rw [crossCochainEquiv_v,
    Cochain.comp_v x.1 (Cochain.ofHom v) (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v (x.1.map (jFunctor k R F)) (Cochain.ofHom (crossChainMap v))
      (add_zero n) i j j hij (add_zero j)]
  simp only [Cochain.ofHom_v, Cochain.map_v]
  exact crossHomAdd_source _ _

theorem crossCohomology_precomp (x : CohomologyClass P P n) :
    crossCohomologyEquiv P P n (fullHomPrecomp v n
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x)) =
      fullHomPrecomp (crossChainMap v) n (mapFullHom (eFunctor k R F) P P n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [mapFullHom_mk, fullHomPrecomp_mk, crossCohomologyEquiv_mk,
    mapFullHom_mk, fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  change crossCochainEquiv P P n ((Cochain.ofHom v).comp
      (x.1.map (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F))) (zero_add n)) =
    (Cochain.ofHom (crossChainMap v)).comp (x.1.map (eFunctor k R F)) (zero_add n)
  apply Cochain.ext
  intro i j hij
  rw [crossCochainEquiv_v,
    Cochain.comp_v (Cochain.ofHom v)
      (x.1.map (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)))
      (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v (Cochain.ofHom (crossChainMap v)) (x.1.map (eFunctor k R F))
      (zero_add n) i i j (add_zero i) hij]
  simp only [Cochain.ofHom_v, Cochain.map_v]
  exact crossHomAdd_target _ _

def tensorComparison : (CohomologyClass P P n × CohomologyClass P P n) →+
    CohomologyClass P (tensorCochain (k := k) (F := F) P) n where
  toFun x := fullHomPostcomp v n x.2 + (n+1).negOnePow • fullHomPrecomp v n
    (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)
  map_zero' := by simp
  map_add' x y := by simp [smul_add]; abel

theorem cross_tensorComparison (a b : CohomologyClass P P n) :
    crossCohomologyEquiv P P n (tensorComparison v n (a,b)) =
      coneComparison (crossChainMap v) n
        (fullHomCohomologyEquiv (eFunctor k R F) P P n a,
          fullHomCohomologyEquiv (jFunctor k R F) P P n b) := by
  change crossCohomologyEquiv P P n (fullHomPostcomp v n b +
    (n+1).negOnePow • fullHomPrecomp v n
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n a)) = _
  rw [map_add]
  simp only [Units.smul_def, map_zsmul, crossCohomology_postcomp, crossCohomology_precomp]
  rfl

end ArExplicit.TriangularInduction

end

end OAI
