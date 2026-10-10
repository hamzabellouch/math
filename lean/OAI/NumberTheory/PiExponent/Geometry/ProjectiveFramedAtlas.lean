import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

theorem coordinatesMap_congr (k : K →+* Γ(X,⊤)) {a b : σ → Γ(X,⊤)} (h : a = b)
    (i : σ) (ha : a i = 1) (hb : b i = 1) :
    coordinatesMap X k a i ha = coordinatesMap X k b i hb := by
  subst b
  rfl

theorem atlasOfFramedSections_morphism_eq {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (U V : X.OpenCover)
    (e : ∀ i, M.restrict (U.f i) ≅ O (U.X i))
    (f : ∀ j, M.restrict (V.f j) ≅ O (V.X j))
    (a : U.I₀ → σ) (b : V.I₀ → σ)
    (ha : ∀ i, coefficient (e i) (restrictSection (U.f i) (s (a i))) = 1)
    (hb : ∀ j, coefficient (f j) (restrictSection (V.f j) (s (b j))) = 1) :
    (atlasOfFramedSections k s U e a ha).morphism =
      (atlasOfFramedSections k s V f b hb).morphism := by
  apply U.hom_ext
  intro i
  apply (V.pullback₁ (U.f i)).hom_ext
  intro j
  change V.I₀ at j
  change pullback.fst (U.f i) (V.f j) ≫ (U.f i ≫ _) =
    pullback.fst (U.f i) (V.f j) ≫ (U.f i ≫ _)
  have hU : U.f i ≫ (atlasOfFramedSections k s U e a ha).morphism =
      coordinatesMap _ ((U.f i).appTop.hom.comp k)
        (fun q => coefficient (e i) (restrictSection (U.f i) (s q))) (a i) (ha i) :=
    CoordinateAtlas.cover_morphism (atlasOfFramedSections k s U e a ha) i
  have hV : V.f j ≫ (atlasOfFramedSections k s V f b hb).morphism =
      coordinatesMap _ ((V.f j).appTop.hom.comp k)
        (fun q => coefficient (f j) (restrictSection (V.f j) (s q))) (b j) (hb j) :=
    CoordinateAtlas.cover_morphism (atlasOfFramedSections k s V f b hb) j
  rw [hU, ← Category.assoc, pullback.condition, Category.assoc, hV]
  change pullback.fst (U.f i) (V.f j) ≫ coordinatesMap _ _ _ _ _ =
    pullback.snd (U.f i) (V.f j) ≫ coordinatesMap _ _ _ _ _
  rw [coordinatesMap_natural, coordinatesMap_natural]
  obtain ⟨c, hc⟩ := overlap_coefficients (U.f i) (V.f j)
    (pullback.fst (U.f i) (V.f j)) (pullback.snd (U.f i) (V.f j))
    (pullback.condition (f := U.f i) (g := V.f j)) (e i) (f j)
  have hscalar :
      (pullback.fst (U.f i) (V.f j)).appTop.hom.comp ((U.f i).appTop.hom.comp k) =
      (pullback.snd (U.f i) (V.f j)).appTop.hom.comp ((V.f j).appTop.hom.comp k) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun q : pullback (U.f i) (V.f j) ⟶ X => q.appTop.hom)
        (pullback.condition (f := U.f i) (g := V.f j))
  simpa only [hscalar] using coordinatesMap_scale _
    ((pullback.fst (U.f i) (V.f j)).appTop.hom.comp ((U.f i).appTop.hom.comp k))
    _ _ (a i) (b j)
    (by simp only [ha, map_one]) (by simp only [hb, map_one]) c (fun q => hc (s q))

theorem sectionsMorphism_eq_framedAtlas {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : Scheme.OpenCover.{u,u} X) (e : ∀ i, M.restrict (U.f i) ≅ O (U.X i))
    (a : U.I₀ → σ)
    (ha : ∀ i, coefficient (e i) (restrictSection (U.f i) (s (a i))) = 1) :
    sectionsMorphism k s hcover = (atlasOfFramedSections k s U e a ha).morphism := by
  exact atlasOfFramedSections_morphism_eq k s _ U _ e _ a _ ha

theorem sectionsMorphism_eq_of_framed_local {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : Scheme.OpenCover.{u,u} X) (e : ∀ i, M.restrict (U.f i) ≅ O (U.X i))
    (a : U.I₀ → σ)
    (ha : ∀ i, coefficient (e i) (restrictSection (U.f i) (s (a i))) = 1)
    (g : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (hg : ∀ i, coordinatesMap (U.X i) ((U.f i).appTop.hom.comp k)
      (fun j => coefficient (e i) (restrictSection (U.f i) (s j))) (a i) (ha i) = U.f i ≫ g) :
    sectionsMorphism k s hcover = g := by
  refine (sectionsMorphism_eq_framedAtlas k s hcover U e a ha).trans ?_
  apply U.hom_ext
  intro i
  exact (CoordinateAtlas.cover_morphism (atlasOfFramedSections k s U e a ha) i).trans (hg i)

end
end PiExponentSeshadri.Projective

end OAI
