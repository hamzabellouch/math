import OAI.Algebra.AuslanderReiten.Stable.StableHomotopyIso
import OAI.Algebra.AuslanderReiten.Cones.CochainCokernel

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

noncomputable def cochainHomotopyCokernelEquiv
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L) ≃+
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0) :=
  (AddEquiv.ofBijective
    (Functor.mapAddHom (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)))
    ⟨Functor.map_injective _, Functor.map_surjective _⟩).trans
      (homotopyCokernelEquiv hK hL)

@[simp]
theorem cochainHomotopyCokernelEquiv_map
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (f : K ⟶ L) :
    cochainHomotopyCokernelEquiv hK hL ((HomotopyCategory.quotient _ _).map f) =
      StableHom.classOf R _ _ (cokernelMap (extendMap f negIndexEmbedding) 0) := by
  exact homotopyCokernelEquiv_map hK hL _

theorem cochainHomotopyCokernelEquiv_comp
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (hM : ExactProjectiveComplex (chainOfCochain M))
    (f : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L)
    (g : (HomotopyCategory.quotient _ _).obj L ⟶ (HomotopyCategory.quotient _ _).obj M) :
    cochainHomotopyCokernelEquiv hK hM (f ≫ g) =
      StableHom.comp (cochainHomotopyCokernelEquiv hL hM g)
        (cochainHomotopyCokernelEquiv hK hL.toExactProjectiveComplex f) := by
  change homotopyCokernelEquiv hK hM
    ((negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).map (f ≫ g)) = _
  erw [Functor.map_comp, homotopyCokernelEquiv_comp hK hL hM]
  rfl

@[simp]
theorem stableCochainHomotopyIso_hom
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (e : StableIsomorphism R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0)) :
    cochainHomotopyCokernelEquiv hK hL.toExactProjectiveComplex
      (stableCochainHomotopyIso hK hL e).hom = e.hom := by
  change homotopyCokernelEquiv hK hL.toExactProjectiveComplex
    ((negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).map
      ((negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).preimageIso
        (stableHomotopyIso hK hL e)).hom) = _
  erw [Functor.preimageIso_hom, Functor.map_preimage, stableHomotopyIso_hom]

noncomputable def cochainHomotopyRawEquiv
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L) ≃+
      StableHom R (CochainCokernel K) (CochainCokernel L) :=
  (cochainHomotopyCokernelEquiv hK hL).trans
    (((StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv K).symm).sourceAddEquiv).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv L)).targetAddEquiv)

@[simp]
theorem cochainHomotopyRawEquiv_map
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (f : K ⟶ L) :
    cochainHomotopyRawEquiv hK hL ((HomotopyCategory.quotient _ _).map f) =
      StableHom.classOf R _ _ (cochainCokernelMap f) := by
  simp only [cochainHomotopyRawEquiv, AddEquiv.trans_apply, cochainHomotopyCokernelEquiv_map,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    StableHom.comp_classOf]
  congr 1
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural f)
    ((cochainCokernelLinearEquiv K).symm x)
  simpa using h

end ArExplicit.CompleteComparison

end OAI
