import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SectionIdealExt

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme}

lemma restrictSection_scalar (φ : Y ⟶ X) [IsOpenImmersion φ]
    {M : X.Modules} (a : Γ(X, ⊤)) (s : O X ⟶ M) :
    restrictSection φ (scalarEnd a ≫ s) = scalarEnd (φ.appTop a) ≫ restrictSection φ s := by
  have h : restrictSection φ (scalarEnd a) ≫ (Scheme.Modules.restrictUnitIso φ).hom =
      scalarEnd (φ.appTop a) := by
    apply endValue_injective
    exact (endValue_restrict φ (scalarEnd a)).trans
      ((congrArg φ.appTop (endValue_scalarEnd a)).trans (endValue_scalarEnd _).symm)
  rw [← h]
  let restriction : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
  let unitIso : restriction.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
  change unitIso.inv ≫ restriction.map (scalarEnd a ≫ s) =
    (unitIso.inv ≫ restriction.map (scalarEnd a) ≫ unitIso.hom) ≫
      unitIso.inv ≫ restriction.map s
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionCombination_restrict {Y : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (v : σ → K) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    restrictSection φ (sectionCombination k s v) =
      sectionCombination (φ.appTop.hom.comp k) (fun i => restrictSection φ (s i)) v := by
  simp only [sectionCombination, restrictSection_sum, restrictSection_scalar, RingHom.comp_apply]

def principalGlobalIdeal (a : Γ(X, ⊤)) : X.IdealSheafData where
  ideal U := Ideal.span {X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op a}
  map_ideal_basicOpen U r := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op ≫
      X.presheaf.map (homOfLE (X.basicOpen_le r)).op) a = _
    rw [← CategoryTheory.Functor.map_comp]
    rfl

@[simp] lemma principalGlobalIdeal_top [IsAffine X] (a : Γ(X, ⊤)) :
    (principalGlobalIdeal a).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a} := by
  change Ideal.span {X.presheaf.map (𝟙 _) a} = _
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma sectionIdeal_framed {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (e : M ≅ O X) :
    sectionIdeal k s hs v = principalGlobalIdeal (coefficient e (sectionCombination k s v)) := by
  apply idealSheaf_ext_local
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ x))
  obtain ⟨_, ⟨U, hUa, rfl⟩, hx, hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (SectionOpens.isoOpen (s i)).isOpen
  let A : X.affineOpens := ⟨U, hUa⟩
  refine ⟨A, hx, ?_⟩
  rw [sectionIdeal_on_frame k s hs v A i hU (restrictFrame A.1.ι e), coefficient_restrict]
  congr 2
  change (A.1.ι.appTop ≫ A.1.topIso.hom) _ = _
  apply congrArg (fun morphism : Γ(X, ⊤) ⟶ Γ(X, A.1) =>
    morphism (coefficient e (sectionCombination k s v)))
  rw [A.1.ι_appTop, A.1.topIso_hom]
  exact (X.presheaf.map_comp _ _).symm

lemma sectionIdeal_on_any_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s v)))} := by
  have h := congrArg (fun J : U.1.toScheme.IdealSheafData =>
    J.ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩)
    (sectionIdeal_framed (U.1.ι.appTop.hom.comp k)
      (fun i => restrictSection U.1.ι (s i)) (restricted_sections_cover s hs U.1.ι) v e)
  rw [← sectionIdeal_restrict k s hs v U.1.ι, comap_ι_top,
    principalGlobalIdeal_top, ← sectionCombination_restrict] at h
  have h' := congrArg (Ideal.map U.1.topIso.hom.hom) h
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at h'
  have hid : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ :=
    congrArg CommRingCat.Hom.hom U.1.topIso.inv_hom_id
  simpa only [hid, Ideal.map_id] using h'

end
end MaximalSeshadri.Projective
end


end
end

end OAI
