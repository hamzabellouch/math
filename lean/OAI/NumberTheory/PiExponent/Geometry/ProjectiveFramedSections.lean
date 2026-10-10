import OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

def framedSectionsMorphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s (X.openCoverOfIsOpenCover U hc) e a hnorm).morphism

@[reassoc]
lemma framedSectionsMorphism_local (i : ι) :
    (U i).ι ≫ framedSectionsMorphism k s U hc e a hnorm =
      coordinatesMap (U i).toScheme ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))) (a i) (hnorm i) :=
  CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s (X.openCoverOfIsOpenCover U hc) e a hnorm) i

theorem framedSectionsMorphism_preimage (j : σ) :
    framedSectionsMorphism k s U hc e a hnorm ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, U i := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have H : (U i).ι ⁻¹ᵁ (framedSectionsMorphism k s U hc e a hnorm ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      (U i).ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, framedSectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) (U i).ι (e i)]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : (U i).toScheme)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

theorem framedSectionsMorphism_closed
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))]
    (hU : ∀ i, SectionOpens.isoOpen (s (a i)) = U i)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))))) :
    IsClosedImmersion (framedSectionsMorphism k s U hc e a hnorm) := by
  let V (i : ι) := Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X (a i))
  let k' (i : ι) := (U i).ι.appTop.hom.comp k
  let b (i : ι) (j : σ) := coefficient (e i) (restrictSection (U i).ι (s j))
  let g (i : ι) := (U i).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom (k' i) (b i)) (MvPolynomial.X (a i))
      (by simpa only [eval₂Hom_X', b, hnorm] using (isUnit_one : IsUnit (1 : Γ((U i).toScheme, ⊤))))))
  let ep (i : ι) := Proj.basicOpenIsoSpec (homogeneousSubmodule σ K) (MvPolynomial.X (a i))
    (isHomogeneous_X K (a i)) (by decide : 0 < (1 : ℕ))
  apply PiExponentSeshadri.Geometry.closedImmersion_of_source_charts
    (framedSectionsMorphism k s U hc e a hnorm) U V hc (fun i => g i ≫ (ep i).inv)
  · intro i
    let : IsAffine (U i).toScheme := haff i
    have : IsClosedImmersion (g i) := normalized_coordinates_closed (k' i) (b i) (a i) (hnorm i) (hgen i)
    infer_instance
  · intro i
    rw [framedSectionsMorphism_local]
    rfl
  · intro i
    exact (framedSectionsMorphism_preimage k s U hc e a hnorm (a i)).trans (hU i)

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ ι κ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem framedSectionsMorphism_eq (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)
    (V : κ → X.Opens) (hd : (⨆ i, V i) = ⊤)
    (d : ∀ i, M.restrict (V i).ι ≅ O (V i).toScheme) (b : κ → σ)
    (hnorm' : ∀ i, coefficient (d i) (restrictSection (V i).ι (s (b i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm =
      framedSectionsMorphism k s V hd d b hnorm' := by
  let W : ι ⊕ κ → X.Opens := Sum.elim U V
  have hw : (⨆ i, W i) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact le_iSup W (Sum.inl i)
  let E : ∀ i, M.restrict (W i).ι ≅ O (W i).toScheme :=
    fun i => match i with | Sum.inl j => e j | Sum.inr j => d j
  let A : ι ⊕ κ → σ := Sum.elim a b
  have hN : ∀ i, coefficient (E i) (restrictSection (W i).ι (s (A i))) = 1 := by
    rintro (i | i)
    · exact hnorm i
    · exact hnorm' i
  let F := framedSectionsMorphism k s W hw E A hN
  have hleft : framedSectionsMorphism k s U hc e a hnorm = F := by
    apply (X.openCoverOfIsOpenCover U hc).hom_ext
    intro i
    change ι at i
    change (U i).ι ≫ _ = (U i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inl i)).symm
  have hright : framedSectionsMorphism k s V hd d b hnorm' = F := by
    apply (X.openCoverOfIsOpenCover V hd).hom_ext
    intro i
    change κ at i
    change (V i).ι ≫ _ = (V i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inr i)).symm
  exact hleft.trans hright.symm

lemma framedSectionsMorphism_eq_sectionsMorphism (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm = sectionsMorphism k s hs :=
  framedSectionsMorphism_eq k s U hc e a hnorm
    (fun i => SectionOpens.isoOpen (s i)) hs (fun i => sectionFrame (s i)) id
    (fun i => sectionFrame_normalized (s i))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}} {M N : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_postcomp (f : M ≅ N) (φ : X.Opens)
    (e : M.restrict φ.ι ≅ O φ.toScheme) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctor φ.ι).mapIso f.symm ≪≫ e)
      (restrictSection φ.ι (s ≫ f.hom)) = coefficient e (restrictSection φ.ι s) := by
  simp only [restrictSection]
  let F : X.Modules ⥤ φ.toScheme.Modules := Scheme.Modules.restrictFunctor φ.ι
  let a : O φ.toScheme ⟶ F.obj (O X) := (Scheme.Modules.restrictUnitIso φ.ι).inv
  let e' : F.obj M ≅ O φ.toScheme := e
  change endValue ((a ≫ F.map (s ≫ f.hom)) ≫ F.map f.inv ≫ e'.hom) =
    endValue ((a ≫ F.map s) ≫ e'.hom)
  have hs : (s ≫ f.hom) ≫ f.inv = s := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm : F.map (s ≫ f.hom) ≫ F.map f.inv = F.map s :=
    (F.map_comp _ _).symm.trans (congrArg F.map hs)
  apply congrArg endValue
  calc
    _ = a ≫ ((F.map (s ≫ f.hom) ≫ F.map f.inv) ≫ e'.hom) := by
      simp only [Category.assoc]
    _ = a ≫ (F.map s ≫ e'.hom) := congrArg (fun t => a ≫ t ≫ e'.hom) hm
    _ = _ := (Category.assoc _ _ _).symm

theorem sectionsMorphism_transport (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : M ≅ N) (ht : (⨆ i, SectionOpens.isoOpen (s i ≫ f.hom)) = ⊤) :
    sectionsMorphism k (fun i => s i ≫ f.hom) ht = sectionsMorphism k s hs := by
  let U (i : σ) := SectionOpens.isoOpen (s i)
  let e (i : σ) := (Scheme.Modules.restrictFunctor (U i).ι).mapIso f.symm ≪≫ sectionFrame (s i)
  have he (i j : σ) : coefficient (e i) (restrictSection (U i).ι (s j ≫ f.hom)) =
      coefficient (sectionFrame (s i)) (restrictSection (U i).ι (s j)) :=
    coefficient_postcomp f (U i) (sectionFrame (s i)) (s j)
  have hn (i : σ) : coefficient (e i) (restrictSection (U i).ι (s i ≫ f.hom)) = 1 := by
    rw [he]
    exact sectionFrame_normalized (s i)
  rw [← framedSectionsMorphism_eq_sectionsMorphism k (fun i => s i ≫ f.hom) ht U hs e id hn]
  apply (X.openCoverOfIsOpenCover U hs).hom_ext
  intro i
  change σ at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [framedSectionsMorphism_local, sectionsMorphism_local]
  congr 1
  funext j
  exact he i j

end PiExponentSeshadri.Projective

end

end OAI
