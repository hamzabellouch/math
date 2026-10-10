import OAI.Algebra.AuslanderReiten.Complete.CompleteStableComparison
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]

def negIndexEmbedding : (ComplexShape.up ℤ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun i : ℤ => -i) neg_injective (by
    intro i j
    change i + 1 = j ↔ -j + 1 = -i
    omega)

instance : negIndexEmbedding.IsRelIff := by
  dsimp [negIndexEmbedding]
  infer_instance

noncomputable abbrev chainOfCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
  K.extend negIndexEmbedding

private instance negIndexFunctor_additive :
    (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).Additive := by
  have := Functor.additive_of_iso
    (negIndexEmbedding.extendHomotopyFunctorFactors (ModuleCat.{u} R)).symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)) _

noncomputable def fullHomStableEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧))) :
    CochainComplex.HomComplex.CohomologyClass K L n ≃+
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain (L⟦n⟧)) 0) :=
  CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
    ((AddEquiv.ofBijective
      (Functor.mapAddHom (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)))
      ⟨Functor.map_injective _, Functor.map_surjective _⟩).trans
        (homotopyCokernelEquiv hK hL))

theorem fullHomStableEquiv_eq_zero_iff
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧)))
    (x : CochainComplex.HomComplex.CohomologyClass K L n) :
    fullHomStableEquiv K L n hK hL x = 0 ↔ x = 0 :=
  map_eq_zero_iff (fullHomStableEquiv K L n hK hL) (fullHomStableEquiv K L n hK hL).injective

end ArExplicit.CompleteComparison

end OAI
