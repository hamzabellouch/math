import OAI.Geometry.SingularHomology.SingularCoverNaturality
import OAI.Geometry.SingularHomology.SimplicialMayerVietoris

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularCover

variable {K L : SSet}

abbrev restrict (f : K ⟶ L) (A : K.Subcomplex) (B : L.Subcomplex)
    (h : A ≤ B.preimage f) : (A : SSet) ⟶ (B : SSet) :=
  restrictedMap f A B h

@[simp, reassoc] theorem restrict_ι (f : K ⟶ L)
    (A : K.Subcomplex) (B : L.Subcomplex) (h : A ≤ B.preimage f) :
    restrict f A B h ≫ B.ι = A.ι ≫ f := rfl

theorem inf_le_preimage (f : K ⟶ L)
    (A B : K.Subcomplex) (A' B' : L.Subcomplex)
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    A ⊓ B ≤ (A' ⊓ B').preimage f := preserves_inter f hA hB

theorem sup_le_preimage (f : K ⟶ L)
    (A B : K.Subcomplex) (A' B' : L.Subcomplex)
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    A ⊔ B ≤ (A' ⊔ B').preimage f := preserves_union f hA hB

abbrev chainsFunctor :=
  ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ))

theorem connecting_naturality (f : K ⟶ L)
    (A B : K.Subcomplex) (A' B' : L.Subcomplex)
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) (n : ℕ) :
    SimplicialMayerVietoris.connecting A B n ≫
        HomologicalComplex.homologyMap
          (chainsFunctor.map (restrict f (A ⊓ B) (A' ⊓ B')
            (inf_le_preimage f A B A' B' hA hB))) n =
      HomologicalComplex.homologyMap
          (chainsFunctor.map (restrict f (A ⊔ B) (A' ⊔ B')
            (sup_le_preimage f A B A' B' hA hB))) (n + 1) ≫
        SimplicialMayerVietoris.connecting A' B' n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (unionShortComplexMap f hA hB)
    (unionShortComplex_shortExact A B) (unionShortComplex_shortExact A' B')
    (n + 1) n rfl

theorem connecting_naturality_apply (f : K ⟶ L)
    (A B : K.Subcomplex) (A' B' : L.Subcomplex)
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) (n : ℕ)
    (v : ((A ⊔ B).toSSet.homology (ModuleCat.of ℝ ℝ) (n + 1) : ModuleCat ℝ)) :
    SimplicialMayerVietoris.connecting A' B' n
        (HomologicalComplex.homologyMap
          (chainsFunctor.map (restrict f (A ⊔ B) (A' ⊔ B')
            (sup_le_preimage f A B A' B' hA hB))) (n + 1) v) =
      HomologicalComplex.homologyMap
          (chainsFunctor.map (restrict f (A ⊓ B) (A' ⊓ B')
            (inf_le_preimage f A B A' B' hA hB))) n
        (SimplicialMayerVietoris.connecting A B n v) := by
  exact (congrArg (fun g => g.hom v) (connecting_naturality f A B A' B' hA hB n)).symm

section ContinuousMaps

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem supported_le_preimage_of_mapsTo
    (f : X → Y) (hf : Continuous f) (U : Set X) (V : Set Y)
    (hUV : Set.MapsTo f U V) :
    supported U ≤ (supported V).preimage
      (TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf))) := by
  intro n σ hσ p
  exact hUV (hσ p)

def continuousUnionShortComplexMap
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    unionShortComplex (supported U) (supported V) ⟶
      unionShortComplex (supported U') (supported V') :=
  unionShortComplexMap (TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf)))
    (supported_le_preimage_of_mapsTo f hf U U' hU)
    (supported_le_preimage_of_mapsTo f hf V V' hV)

end ContinuousMaps

end Problem340.SingularCover

end

end OAI
