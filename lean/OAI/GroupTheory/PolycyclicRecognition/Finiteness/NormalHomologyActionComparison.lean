import OAI.GroupTheory.PolycyclicRecognition.Algebra.TrivialBarCoinvariants
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RepresentationHomologyAction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalDerivedHomologyFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyQuotient

namespace OAI

/-! # The canonical quotient action agrees with conjugation

The comparison uses the actual inclusion of subgroup bar chains. Inner bar
translation is homotopic to the identity before passing to coinvariants.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

abbrev normalBarComplex : ChainComplex (Rep.{0} ℤ (G ⧸ N)) ℕ :=
  ((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Rep.barComplex ℤ G)

abbrev normalBarInnerMap (g : G) :
    ((forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalBarComplex N) ⟶
    ((forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalBarComplex N) :=
  ((Rep.resFunctor.{0} N.subtype ⋙ Rep.coinvariantsFunctor ℤ N).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (innerBarMap g)

theorem normalSubgroupBarChains_conjugation [DecidableEq N] (g : G) :
    groupHomology.chainsMap (MulAut.conjNormal (H := N) g).toMonoidHom
        (normalHomologyCoefficient ℤ N (trivialIntegral G) g) ≫
      normalSubgroupBarChains N =
    normalSubgroupBarChains N ≫ normalBarInnerMap N g ≫
      underlyingChainAction (normalBarComplex N) (QuotientGroup.mk' N g) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro r
  change (normalSubgroupBarChains N).f i
      ((groupHomology.chainsMap (MulAut.conjNormal (H := N) g).toMonoidHom
        (normalHomologyCoefficient ℤ N (trivialIntegral G) g)).f i
          (Finsupp.single x r)) = _
  rw [groupHomology.chainsMap_f_single]
  change (normalSubgroupBarChains N).f i
      (Finsupp.single ((MulAut.conjNormal (H := N) g) ∘ x) r) =
    (underlyingChainAction (normalBarComplex N) (QuotientGroup.mk' N g)).f i
      ((normalBarInnerMap N g).f i
        ((normalSubgroupBarChains N).f i (Finsupp.single x r)))
  rw [normalSubgroupBarChains_single, normalSubgroupBarChains_single]
  change Representation.Coinvariants.mk _
      (Finsupp.single (N.subtype ∘ ((MulAut.conjNormal (H := N) g) ∘ x))
        (MonoidAlgebra.single 1 r)) =
    Representation.Coinvariants.mk _
      ((Representation.free ℤ G (Fin i → G)) g
        ((innerBarFreeMap g i).hom
          (Finsupp.single (N.subtype ∘ x) (MonoidAlgebra.single 1 r))))
  rw [innerBarFreeMap_single, Representation.free_single_single]
  simp only [one_mul, mul_inv_cancel]
  rfl

theorem normalBarInnerMap_homology (g : G) (i : ℕ) :
    HomologicalComplex.homologyMap (normalBarInnerMap N g) i = 𝟙 _ := by
  let F := Rep.resFunctor.{0} N.subtype ⋙ Rep.coinvariantsFunctor ℤ N
  let T := F.mapHomologicalComplex (ComplexShape.down ℕ)
  have h := (F.mapHomotopy (innerBarMapHomotopy g)).homologyMap_eq i
  have hId : T.map (𝟙 (Rep.barComplex ℤ G)) = 𝟙 (T.obj (Rep.barComplex ℤ G)) :=
    T.map_id _
  change HomologicalComplex.homologyMap (T.map (innerBarMap g)) i =
    HomologicalComplex.homologyMap (T.map (𝟙 (Rep.barComplex ℤ G))) i at h
  rw [hId, HomologicalComplex.homologyMap_id] at h
  exact h

theorem normalSubgroupBarHomology_conjugation [DecidableEq N] (g : G) (i : ℕ) :
    normalHomologyMap ℤ N (trivialIntegral G) i g ≫
      HomologicalComplex.homologyMap (normalSubgroupBarChains N) i =
    HomologicalComplex.homologyMap (normalSubgroupBarChains N) i ≫
      HomologicalComplex.homologyMap
        (underlyingChainAction (normalBarComplex N) (QuotientGroup.mk' N g)) i := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (normalSubgroupBarChains_conjugation N g)
  have hi := HomologicalComplex.homologyMap_comp (normalBarInnerMap N g)
    (underlyingChainAction (normalBarComplex N) (QuotientGroup.mk' N g)) i
  rw [normalBarInnerMap_homology, Category.id_comp] at hi
  exact (HomologicalComplex.homologyMap_comp _ _ i).symm.trans
    (h.trans ((HomologicalComplex.homologyMap_comp _ _ i).trans
      (congrArg (fun k => HomologicalComplex.homologyMap (normalSubgroupBarChains N) i ≫ k) hi)))

end PolycyclicRecognition

end

end OAI
