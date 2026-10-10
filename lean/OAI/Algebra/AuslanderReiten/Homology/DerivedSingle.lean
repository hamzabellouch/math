import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

def derivedSingleIso (K : CochainComplex C ℤ) (n : ℤ)
    (hex : ∀ i : ℤ, i ≠ n → K.ExactAt i) :
    DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor C n).obj (K.homology n) := Classical.choice (by
  let : K.IsGE n := (CochainComplex.isGE_iff K n).mpr (fun i hi => hex i (ne_of_lt hi))
  let : K.IsLE n := (CochainComplex.isLE_iff K n).mpr (fun i hi => hex i (ne_of_gt hi))
  let : (DerivedCategory.Q.obj K).IsGE n := (DerivedCategory.isGE_Q_obj_iff K n).mpr inferInstance
  let : (DerivedCategory.Q.obj K).IsLE n := (DerivedCategory.isLE_Q_obj_iff K n).mpr inferInstance
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj K) n
  let h : K.homology n ≅ M :=
    ((DerivedCategory.homologyFunctorFactors C n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C n).mapIso h.symm⟩)

end ArExplicit

end

end OAI
