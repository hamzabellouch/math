import OAI.Algebra.AuslanderReiten.Stable.StableIsomorphism
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComparison

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

@[simp]
theorem homotopyCokernelEquiv_id (hP : TotallyAcyclicComplex P) :
    homotopyCokernelEquiv hP hP.toExactProjectiveComplex (𝟙 _) = StableHom.identity := by
  rw [← (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).map_id,
    homotopyCokernelEquiv_map, cokernelMap_id]
  rfl

noncomputable def stableHomotopyIso (hP : TotallyAcyclicComplex P)
    (hQ : TotallyAcyclicComplex Q) (e : StableIsomorphism R (Cokernel P 0) (Cokernel Q 0)) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj P ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj Q where
  hom := (homotopyCokernelEquiv hP hQ.toExactProjectiveComplex).symm e.hom
  inv := (homotopyCokernelEquiv hQ hP.toExactProjectiveComplex).symm e.inv
  hom_inv_id := by
    apply (homotopyCokernelEquiv hP hP.toExactProjectiveComplex).injective
    rw [homotopyCokernelEquiv_comp hP hQ hP.toExactProjectiveComplex,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, homotopyCokernelEquiv_id]
    exact e.hom_inv_id
  inv_hom_id := by
    apply (homotopyCokernelEquiv hQ hQ.toExactProjectiveComplex).injective
    rw [homotopyCokernelEquiv_comp hQ hP hQ.toExactProjectiveComplex,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, homotopyCokernelEquiv_id]
    exact e.inv_hom_id

@[simp]
theorem stableHomotopyIso_hom (hP : TotallyAcyclicComplex P)
    (hQ : TotallyAcyclicComplex Q) (e : StableIsomorphism R (Cokernel P 0) (Cokernel Q 0)) :
    homotopyCokernelEquiv hP hQ.toExactProjectiveComplex (stableHomotopyIso hP hQ e).hom =
      e.hom := AddEquiv.apply_symm_apply _ _

noncomputable def stableCochainHomotopyIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (e : StableIsomorphism R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0)) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L :=
  (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).preimageIso
    (stableHomotopyIso hK hL e)

end ArExplicit.CompleteComparison

end OAI
