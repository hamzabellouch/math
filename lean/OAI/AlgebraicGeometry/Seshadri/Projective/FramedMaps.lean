import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PowerExtension
import OAI.AlgebraicGeometry.Seshadri.Projective.ClosedEmbedding

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
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
  apply MaximalSeshadri.Geometry.closedImmersion_of_source_charts
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
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
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
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

lemma isIso_restricted_section {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : SectionOpens.isoOpen s = U) : IsIso (restrictSection U.ι s) := by
  subst U
  exact (sectionFrame s).isIso_inv

theorem LineBundle.power_extension_ratio [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ((sectionOpen X s).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := L.power_extension s hD ((sectionOpen X s).topIso.hom f)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := hN n hn
  refine ⟨t, ?_⟩
  apply (openSectionEquiv (modulePow X L.sheaf n) (sectionOpen X s)).injective
  erw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict]
  exact ht

lemma coefficient_ratio {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ O U.toScheme) (s t : O X ⟶ M)
    (f : Γ(U.toScheme, ⊤)) (hs : coefficient e (restrictSection U.ι s) = 1)
    (ht : restrictSection U.ι t = scalarEnd f ≫ restrictSection U.ι s) :
    coefficient e (restrictSection U.ι t) = f := by
  rw [ht]
  change endValue (scalarEnd f ≫ restrictSection U.ι s ≫ e.hom) = f
  rw [endValue_comp, endValue_scalarEnd]
  change f * coefficient e (restrictSection U.ι s) = f
  rw [hs, mul_one]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme} {K ι : Type} [CommRing K] [Fintype ι]

theorem LineBundle.power_section_embedding [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] (L : LineBundle X)
    (s : ι → GlobalSections X L.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (sectionOpen X (s i)))
    (hne : ∀ i, (sectionOpen X (s i) : Set X).Nonempty) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U (i : ι) := sectionOpen X (s i)
  have hfinite (i : ι) : ∃ m : ℕ, ∃ b : Fin m → Γ((U i).toScheme, ⊤),
      Function.Surjective (eval₂Hom ((U i).ι.appTop.hom.comp k) b) := by
    let : IsAffine (U i).toScheme := haff i
    obtain ⟨m, b, hb⟩ := affine_coordinate_generators ((U i).ι ≫ p)
    refine ⟨m, b, ?_⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc, k] using hb
  choose m b hb using hfinite
  choose N hN using fun i j => L.power_extension_ratio (s i) (hne i) (b i j)
  let n := max 1 (Finset.univ.sup (fun v : (i : ι) × Fin (m i) => N v.1 v.2))
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hn' (i : ι) (j : Fin (m i)) : N i j ≤ n :=
    (Finset.le_sup (f := fun v : (i : ι) × Fin (m i) => N v.1 v.2)
      (Finset.mem_univ ⟨i, j⟩)).trans (le_max_right _ _)
  choose t ht using fun i j => hN i j n (hn' i j)
  let σ := ι ⊕ ((i : ι) × Fin (m i))
  let S : σ → GlobalSections X (modulePow X L.sheaf n) :=
    Sum.elim (fun i => powerSection (s i) n) (fun v => t v.1 v.2)
  have hU (i : ι) : SectionOpens.isoOpen (S (Sum.inl i)) = U i :=
    L.sectionOpen_power (s i) hn
  have hSn (i : ι) : IsIso (restrictSection (U i).ι (S (Sum.inl i))) :=
    isIso_restricted_section _ _ (hU i)
  let e (i : ι) : (modulePow X L.sheaf n).restrict (U i).ι ≅ O (U i).toScheme :=
    (asIso (restrictSection (U i).ι (S (Sum.inl i)))).symm
  have hnorm (i : ι) : coefficient (e i) (restrictSection (U i).ι (S (Sum.inl i))) = 1 :=
    coefficient_frame (e i)
  have hS : (⨆ v, SectionOpens.isoOpen (S v)) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact (le_of_eq (hU i).symm).trans (le_iSup (fun v : σ => SectionOpens.isoOpen (S v)) (Sum.inl i))
  have hproper : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
    rw [toSpec_scalarMap]
    infer_instance
  have hgen (i : ι) : Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun v => coefficient (e i) (restrictSection (U i).ι (S v)))) := by
    have heq : (fun v => coefficient (e i) (restrictSection (U i).ι (S v))) ∘
        (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) = b i := by
      funext j
      exact coefficient_ratio (e i) (S (Sum.inl i)) (S (Sum.inr ⟨i, j⟩)) (b i j)
        (hnorm i) (ht i j)
    intro r
    obtain ⟨q, hq⟩ := hb i r
    refine ⟨rename (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) q, ?_⟩
    rw [eval₂Hom_rename, heq]
    exact hq
  have hclosed := framedSectionsMorphism_closed k S U hc e Sum.inl hnorm hU
    (fun i => haff i) hgen
  rw [framedSectionsMorphism_eq_sectionsMorphism k S hS U hc e Sum.inl hnorm] at hclosed
  exact ⟨n, hn, σ, inferInstance, S, hS, hclosed⟩

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}} {M N : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_postcomp (f : M ≅ N) (φ : X.Opens)
    (e : M.restrict φ.ι ≅ O φ.toScheme) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctor φ.ι).mapIso f.symm ≪≫ e)
      (restrictSection φ.ι (s ≫ f.hom)) = coefficient e (restrictSection φ.ι s) := by
  change endValue
    (((Scheme.Modules.restrictUnitIso φ.ι).inv ≫
      (Scheme.Modules.restrictFunctor φ.ι).map (s ≫ f.hom)) ≫
      (Scheme.Modules.restrictFunctor φ.ι).map f.inv ≫ e.hom) = _
  erw [Functor.map_comp]
  erw [Category.assoc, Category.assoc,
    ((Scheme.Modules.restrictFunctor φ.ι).mapIso f).hom_inv_id_assoc]
  exact congrArg endValue (Category.assoc _ _ _).symm

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

end
end MaximalSeshadri.Projective


end
end
end

end OAI
