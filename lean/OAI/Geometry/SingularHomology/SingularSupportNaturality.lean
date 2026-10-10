import OAI.Geometry.SingularHomology.SingularCoverChains
import OAI.Geometry.SingularHomology.SingularSmallChains

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

theorem singularCover_supported_eq_inSubset
    {X : Type} [TopologicalSpace X] (s : Set X) :
    SingularCover.supported s = SingularSmallChains.inSubset s := rfl

namespace SingularSmallChains

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[reassoc] theorem subspaceIso_hom_inclusion (s : Set X) :
    (subspaceIso s).hom ≫ (inSubset s).ι =
      TopCat.toSSet.map (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := by
  rfl

def restrictMap (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) : C(s, t) :=
  ⟨fun x => ⟨f x.val, hst x.property⟩,
    (hf.comp continuous_subtype_val).subtype_mk _⟩

def mapInSubset (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) : (inSubset s : SSet) ⟶ inSubset t where
  app n := TypeCat.ofHom fun σ =>
    ⟨(TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf))).app n σ.val,
      fun p => hst (σ.property p)⟩
  naturality := by
    intro n m g
    ext σ
    apply Subtype.ext
    rfl

@[reassoc] theorem subspaceIso_naturality
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) :
    TopCat.toSSet.map (TopCat.ofHom (restrictMap f hf s t hst)) ≫
        (subspaceIso t).hom =
      (subspaceIso s).hom ≫ mapInSubset f hf s t hst := by
  rfl

@[reassoc] theorem mapInSubset_inclusion
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) :
    mapInSubset f hf s t hst ≫ (inSubset t).ι =
      (inSubset s).ι ≫ TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf)) := by
  rfl

theorem subspaceHomologyIso_inclusion_apply (s : Set X) (n : ℕ)
    (v : RealSingularHomology n s) :
    (SSet.homologyMap (inSubset s).ι (ModuleCat.of ℝ ℝ) n).hom
        ((subspaceHomologyIso s n).toLinearEquiv v) =
      realHomologyMap n (Subtype.val : s → X) continuous_subtype_val v := by
  have h := congrArg (fun k => (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).map k)
    (subspaceIso_hom_inclusion s)
  rw [Functor.map_comp] at h
  exact congrArg (fun k : RealSingularHomology n s ⟶ RealSingularHomology n X =>
    k.hom v) h

theorem subspaceHomologyIso_naturality_apply
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (hst : Set.MapsTo f s t) (n : ℕ) (v : RealSingularHomology n s) :
    (subspaceHomologyIso t n).toLinearEquiv
        (realHomologyMap n (restrictMap f hf s t hst)
          (restrictMap f hf s t hst).continuous v) =
      (SSet.homologyMap (mapInSubset f hf s t hst) (ModuleCat.of ℝ ℝ) n).hom
        ((subspaceHomologyIso s n).toLinearEquiv v) := by
  have h := congrArg (fun k => (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).map k)
    (subspaceIso_naturality f hf s t hst)
  simp only [Functor.map_comp] at h
  exact congrArg (fun k : RealSingularHomology n s ⟶
      (inSubset t : SSet).homology (ModuleCat.of ℝ ℝ) n => k.hom v) h

end SingularSmallChains
end Problem340

end

end OAI
