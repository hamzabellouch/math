import OAI.Algebra.AuslanderReiten.Complete.CompleteNullhomotopy
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

def stableCokernel : (P ⟶ Q) →+ StableHom R (Cokernel P 0) (Cokernel Q 0) where
  toFun F := StableHom.classOf R _ _ (cokernelMap F 0)
  map_zero' := by simp
  map_add' F G := by simp

theorem stableCokernel_surjective (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) : Function.Surjective (stableCokernel (P := P) (Q := Q)) := by
  intro x
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective x
  obtain ⟨F, rfl⟩ := cokernelMap_surjective hP hQ f
  exact ⟨F, rfl⟩

private theorem comparison_kernels (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) :
    (Functor.mapAddHom (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ))
      (X := P) (Y := Q)).ker = (stableCokernel (P := P) (Q := Q)).ker := by
  ext F
  change (HomotopyCategory.quotient _ _).map F = 0 ↔ stableCokernel F = 0
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  exact nullhomotopy_iff_stable_zero hP hQ F

noncomputable def homotopyCokernelEquiv (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) :
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj P ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj Q) ≃+
        StableHom R (Cokernel P 0) (Cokernel Q 0) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (Functor.mapAddHom (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)))
    (Functor.map_surjective _)).symm.trans
      ((QuotientAddGroup.quotientAddEquivOfEq (comparison_kernels hP hQ)).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective stableCokernel
          (stableCokernel_surjective hP hQ)))

@[simp]
theorem homotopyCokernelEquiv_map (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) :
    homotopyCokernelEquiv hP hQ ((HomotopyCategory.quotient _ _).map F) =
      StableHom.classOf R _ _ (cokernelMap F 0) := by
  let f := Functor.mapAddHom
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)) (X := P) (Y := Q)
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f (Functor.map_surjective _)
  have he : e (QuotientAddGroup.mk F) = (HomotopyCategory.quotient _ _).map F := rfl
  change (QuotientAddGroup.quotientKerEquivOfSurjective stableCokernel
    (stableCokernel_surjective hP hQ))
      (QuotientAddGroup.quotientAddEquivOfEq (comparison_kernels hP hQ)
        (e.symm ((HomotopyCategory.quotient _ _).map F))) = _
  rw [← he, e.symm_apply_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

theorem homotopyCokernelEquiv_comp {S : ChainComplex (ModuleCat.{u} R) ℤ}
    (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q)
    (hS : ExactProjectiveComplex S)
    (f : (HomotopyCategory.quotient _ _).obj P ⟶ (HomotopyCategory.quotient _ _).obj Q)
    (g : (HomotopyCategory.quotient _ _).obj Q ⟶ (HomotopyCategory.quotient _ _).obj S) :
    homotopyCokernelEquiv hP hS (f ≫ g) =
      StableHom.comp (homotopyCokernelEquiv hQ hS g)
        (homotopyCokernelEquiv hP hQ.toExactProjectiveComplex f) := by
  obtain ⟨F, rfl⟩ := Functor.map_surjective (HomotopyCategory.quotient _ _) f
  obtain ⟨G, rfl⟩ := Functor.map_surjective (HomotopyCategory.quotient _ _) g
  rw [← Functor.map_comp, homotopyCokernelEquiv_map, homotopyCokernelEquiv_map,
    homotopyCokernelEquiv_map, StableHom.comp_classOf, cokernelMap_comp]

end ArExplicit.CompleteComparison

end OAI
