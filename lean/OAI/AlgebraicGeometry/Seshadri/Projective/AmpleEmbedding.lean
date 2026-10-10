import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.FramedMaps

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

theorem LineBundle.ample_projective_sections [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  obtain ⟨d, hd, l, s, hc, ha, hn⟩ := L.ample_common_degree_cover hL
  obtain ⟨n, hn', σ, hσ, t, ht, he⟩ := (L.pow d).power_section_embedding p s hc ha hn
  let e := linePowerMul L d n
  let T : σ → GlobalSections X (modulePow X L.sheaf (d*n)) := fun i => t i ≫ e.hom
  have hT : (⨆ i, SectionOpens.isoOpen (T i)) = ⊤ := by
    calc
      (⨆ i, SectionOpens.isoOpen (T i)) = ⨆ i, SectionOpens.isoOpen (t i) :=
        iSup_congr fun i => SectionOpens.isoOpen_postcomp (t i) e
      _ = ⊤ := ht
  refine ⟨d*n, Nat.mul_pos hd hn', σ, hσ, T, hT, ?_⟩
  dsimp only [T]
  erw [sectionsMorphism_transport _ t ht e hT]
  exact he

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

lemma constantsInDegreeZero_bijective (N : ℕ) :
    Function.Bijective (constantsInDegreeZero N) := by
  constructor
  · intro a b h
    have h' : MvPolynomial.C a = (MvPolynomial.C b : MvPolynomial (Fin (N + 1)) ℂ) :=
      congrArg Subtype.val h
    exact MvPolynomial.C_injective _ _ h'
  · intro p
    have h : p.val.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.property
    refine ⟨p.val.coeff 0, ?_⟩
    apply Subtype.ext
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

def constantsInDegreeZeroIso (N : ℕ) :
    CommRingCat.of ℂ ≅ CommRingCat.of (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0) :=
  (RingEquiv.ofBijective (constantsInDegreeZero N) (constantsInDegreeZero_bijective N)).toCommRingCatIso

instance constantsInDegreeZero_isIso (N : ℕ) :
    IsIso (CommRingCat.ofHom (constantsInDegreeZero N)) :=
  (constantsInDegreeZeroIso N).isIso_hom

instance projectiveSpaceToSpec_proper (N : ℕ) : IsProper (projectiveSpaceToSpec N) := by
  let A := MvPolynomial (Fin (N + 1)) ℂ
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ
  let : Algebra ℂ (𝒜 0) := SetLike.GradeZero.instAlgebra 𝒜
  let : IsScalarTower ℂ (𝒜 0) A := ⟨fun a b c => by
    change (a • (b : A)) * c = a • ((b : A) * c)
    exact smul_mul_assoc a (b : A) c⟩
  let : Algebra.FiniteType (𝒜 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (𝒜 0) A
  have hp : IsProper (Proj.toSpecZero 𝒜) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat 𝒜
  have : IsIso (Spec.map (CommRingCat.ofHom (constantsInDegreeZero N))) := by infer_instance
  unfold projectiveSpaceToSpec
  exact IsProper.stableUnderComposition.comp_mem _ _ hp inferInstance

instance Surface.proper (S : Surface) : IsProper S.structureMap := by
  rw [← S.overComplex]
  infer_instance

instance Surface.compact (S : Surface) : CompactSpace S.scheme :=
  QuasiCompact.compactSpace_of_compactSpace S.structureMap

instance Surface.locallyNoetherian (S : Surface) : IsLocallyNoetherian S.scheme :=
  LocallyOfFiniteType.isLocallyNoetherian S.structureMap

instance Surface.noetherian (S : Surface) : IsNoetherian S.scheme where

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Projective

theorem Surface.ample_embedding (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections S.scheme (modulePow S.scheme L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) t ht) :=
  L.ample_projective_sections S.structureMap hL

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization MaximalSeshadri.Frames
open scoped AlgebraicGeometry
variable {K R σ : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_eval₂_of_evalAway (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K)
      (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))))) :
    Function.Surjective (eval₂Hom k a) := by
  intro r
  obtain ⟨x, hx⟩ := h r
  obtain ⟨n, q, hq, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ K)
    (isHomogeneous_X K i) x
  refine ⟨q, ?_⟩
  have he := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))) n q hq
  simpa only [hx, eval₂Hom_X', hi, one_pow, mul_one] using he.symm

lemma affine_evaluation_surjective {Y : Scheme.{u}} (f : R →+* Γ(Y, ⊤))
    [IsClosedImmersion (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    Function.Surjective f := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hg := (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hh := hg.comp (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  change Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom at hh
  simpa only [hEq, CommRingCat.hom_ofHom] using hh

theorem sectionsMorphism_chart_generators {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧ Function.Surjective
      (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hs) := by
    refine @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hs) inferInstance (V.map_prop i) ?_ ?_
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsClosedImmersion g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine g).1, ?_⟩
  exact normalized_eval₂_of_evalAway k' a i hi
    (@affine_evaluation_surjective _ _ U.toScheme f hg)

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames
open scoped AlgebraicGeometry
variable {K σ τ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma eval₂_surjective_reindex {R : Type u} [CommRing R] (k : K →+* R)
    (a : σ → R) (e : τ ≃ σ) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (eval₂Hom k (a ∘ e)) := by
  intro r
  obtain ⟨p, hp⟩ := h r
  refine ⟨rename e.symm p, ?_⟩
  change eval₂ k (a ∘ e) (rename e.symm p) = r
  rw [MvPolynomial.eval₂_rename]
  change eval₂ k a p = r at hp
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hp

theorem sectionsMorphism_reindex_closed (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (e : τ ≃ σ)
    (ht : (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤) :
    IsClosedImmersion (sectionsMorphism k (s ∘ e) ht) := by
  apply sectionsMorphism_isClosedImmersion
  · intro i
    exact (sectionsMorphism_chart_generators k s hs (e i)).1
  · intro i
    let U := SectionOpens.isoOpen (s (e i))
    let k' : K →+* Γ(U.toScheme, ⊤) := U.ι.appTop.hom.comp k
    let a : σ → Γ(U.toScheme, ⊤) := fun j =>
      coefficient (sectionFrame (s (e i))) (restrictSection U.ι (s j))
    have h : Function.Surjective (eval₂Hom k' a) :=
      (sectionsMorphism_chart_generators k s hs (e i)).2
    change Function.Surjective (eval₂Hom k' (a ∘ e))
    exact eval₂_surjective_reindex k' a e h

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.ample_embedding_fin (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) :
    ∃ n : ℕ, 0 < n ∧ ∃ N : ℕ,
      ∃ t : Fin (N+1) → GlobalSections S.scheme (modulePow S.scheme L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) t ht) := by
  classical
  obtain ⟨n, hn, σ, hσ, s, hs, hc⟩ := S.ample_embedding L hL
  have hne : Nonempty σ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty S.scheme)
    have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hs]; trivial
    obtain ⟨i, _⟩ := (Opens.mem_iSup).mp hx
    exact ⟨i⟩
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr hne
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (N+1) ≃ σ := ((Fintype.equivFin σ).trans (finCongr hN)).symm
  have ht : (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤ := by
    exact (e.iSup_comp (g := fun j => SectionOpens.isoOpen (s j))).trans hs
  refine ⟨n, hn, N, s ∘ e, ht, ?_⟩
  exact sectionsMorphism_reindex_closed _ s hs e ht

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
