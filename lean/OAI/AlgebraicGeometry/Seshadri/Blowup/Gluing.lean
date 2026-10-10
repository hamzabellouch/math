import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.LocalUniversal

namespace OAI

section
namespace MaximalSeshadri.BlowupGluing
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

abbrev baseCover (_I : X.IdealSheafData) : X.OpenCover := Scheme.AffineZariskiSite.directedCover X

local instance localAffine (U : X.AffineZariskiSite) : IsAffine U.toOpens.toScheme := U.2

abbrev localCentre (U : X.AffineZariskiSite) : U.toOpens.toScheme.IdealSheafData := I.comap U.toOpens.ι

abbrev localScheme (U : X.AffineZariskiSite) : Scheme :=
  AffineBlowup.scheme (localCentre I U)

abbrev localProjection (U : X.AffineZariskiSite) : localScheme I U ⟶ U.toOpens.toScheme :=
  AffineBlowup.projection (localCentre I U)

lemma local_isBlowup (U : X.AffineZariskiSite) :
    IsBlowup (localCentre I U) (localProjection I U) :=
  AffineBlowup.isBlowup (localCentre I U)

lemma centre_transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (localCentre I V).comap ((baseCover I).trans h) = localCentre I U := by
  rw [localCentre, ← Scheme.IdealSheafData.comap_comp]
  change I.comap ((baseCover I).trans h ≫ (baseCover I).f V) = _
  rw [Scheme.Cover.trans_map]

lemma local_invertible {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    InvertiblePullbackIdeal (localCentre I V)
      (localProjection I U ≫ (baseCover I).trans h) := by
  apply (InvertibleLocal.invertible_congr (I' := localCentre I U)
    (f' := localProjection I U) ?_).mpr (local_isBlowup I U).1
  rw [Scheme.IdealSheafData.comap_comp, centre_transition]

def transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    localScheme I U ⟶ localScheme I V :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose

@[reassoc (attr := simp)]
lemma transition_projection {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    transition I h ≫ localProjection I V = localProjection I U ≫ (baseCover I).trans h :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose_spec.1

lemma transition_id (U : X.AffineZariskiSite) : transition I (𝟙 U) = 𝟙 (localScheme I U) := by
  apply (local_isBlowup I U).hom_ext (localProjection I U) (local_isBlowup I U).1
  · rw [transition_projection, Scheme.Cover.trans_id (baseCover I) U, Category.comp_id]
  · simp

lemma transition_comp {U V W : X.AffineZariskiSite} (h : U ⟶ V) (k : V ⟶ W) :
    transition I (h ≫ k) = transition I h ≫ transition I k := by
  apply (local_isBlowup I W).hom_ext _ (local_invertible I (h ≫ k))
  · exact transition_projection I (h ≫ k)
  · rw [Category.assoc, transition_projection, ← Category.assoc, transition_projection,
      Category.assoc, Scheme.Cover.trans_comp (baseCover I) h k]

def diagram : X.AffineZariskiSite ⥤ Scheme where
  obj := localScheme I
  map := transition I
  map_id := transition_id I
  map_comp := transition_comp I

def diagramMap : diagram I ⟶ (baseCover I).functorOfLocallyDirected where
  app := localProjection I
  naturality _ _ h := transition_projection I h

lemma diagramMap_equifibered : (diagramMap I).Equifibered := by
  intro U V h
  apply IsPullback.flip
  change IsPullback (localProjection I U) (transition I h)
    ((baseCover I).trans h) (localProjection I V)
  apply (local_isBlowup I V).baseChangeSquare ((baseCover I).trans h)
    (localProjection I U)
  · rw [centre_transition]
    exact local_isBlowup I U
  · exact transition_projection I h

def gluing : (baseCover I).RelativeGluingData where
  functor := diagram I
  natTrans := diagramMap I
  equifibered := diagramMap_equifibered I

abbrev scheme : Scheme := (gluing I).glued
abbrev projection : scheme I ⟶ X := (gluing I).toBase
abbrev cover : (scheme I).OpenCover := (gluing I).cover

@[reassoc (attr := simp)]
lemma cover_projection (U : X.AffineZariskiSite) :
    (cover I).f U ≫ projection I = localProjection I U ≫ U.toOpens.ι :=
  (gluing I).ι_toBase U

lemma local_pullback (U : X.AffineZariskiSite) :
    IsPullback (localProjection I U) ((cover I).f U) U.toOpens.ι (projection I) :=
  (gluing I).isPullback_natTrans_ι_toBase U

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

lemma projection_invertible : InvertiblePullbackIdeal I (projection I) := by
  apply InvertibleLocal.invertible_of_cover I (projection I) (cover I)
  intro U
  apply (congrArg (InvertiblePullbackIdeal I) (cover_projection I U)).mpr
  apply (InvertibleLocal.invertible_congr
    (Scheme.IdealSheafData.comap_comp I (localProjection I U) U.toOpens.ι)).mpr
  exact (local_isBlowup I U).1

lemma test_invertible {Y : Scheme.{0}} (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (U : X.AffineZariskiSite) :
    InvertiblePullbackIdeal (localCentre I U) (pullback.snd f U.toOpens.ι) := by
  apply (InvertibleLocal.invertible_congr (I' := I)
    (f' := pullback.fst f U.toOpens.ι ≫ f) ?_).mpr
  · exact InvertibleLocal.invertible_restrict_general I f hf (pullback.fst f U.toOpens.ι)
  · change ((I.comap U.toOpens.ι).comap (pullback.snd f U.toOpens.ι)) = _
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition]

lemma hom_ext {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f)
    (g h : Y ⟶ scheme I) (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) : g = h := by
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  apply C.hom_ext
  intro U
  let s := pullback.snd f U.toOpens.ι
  let t := pullback.fst f U.toOpens.ι
  have eg : s ≫ U.toOpens.ι = (t ≫ g) ≫ projection I := by
    rw [Category.assoc, hg]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  have eh : s ≫ U.toOpens.ι = (t ≫ h) ≫ projection I := by
    rw [Category.assoc, hh]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  let g' := (local_pullback I U).lift s (t ≫ g) eg
  let h' := (local_pullback I U).lift s (t ≫ h) eh
  have he : g' = h' := (local_isBlowup I U).hom_ext s (test_invertible I f hf U)
    ((local_pullback I U).lift_fst _ _ _) ((local_pullback I U).lift_fst _ _ _)
  have he' := congrArg (fun k => k ≫ (cover I).f U) he
  change t ≫ g = t ≫ h
  exact ((local_pullback I U).lift_snd s (t ≫ g) eg).symm.trans
    (he'.trans ((local_pullback I U).lift_snd s (t ≫ h) eh))

theorem universal {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f) :
    ∃! h : Y ⟶ scheme I, h ≫ projection I = f := by
  classical
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  let l (U : X.AffineZariskiSite) : C.X U ⟶ localScheme I U :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose
  have hl (U : X.AffineZariskiSite) : l U ≫ localProjection I U = pullback.snd f U.toOpens.ι :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose_spec.1
  let g (U : C.I₀) : C.X U ⟶ scheme I := l U ≫ (cover I).f U
  have hg (U : C.I₀) : g U ≫ projection I = C.f U ≫ f := by
    exact (Category.assoc (l U) ((cover I).f U) (projection I)).trans
      ((congrArg (l U ≫ ·) (cover_projection I U)).trans
        ((Category.assoc (l U) (localProjection I U) U.toOpens.ι).symm.trans
          ((congrArg (· ≫ U.toOpens.ι) (hl U)).trans
            (pullback.condition (f := f) (g := U.toOpens.ι)).symm)))
  have hcompat (U V : C.I₀) : pullback.fst (C.f U) (C.f V) ≫ g U =
      pullback.snd (C.f U) (C.f V) ≫ g V := by
    let j := pullback.fst (C.f U) (C.f V) ≫ C.f U
    apply hom_ext I (j ≫ f)
    · exact InvertibleLocal.invertible_restrict_general I f hf j
    · rw [Category.assoc, hg]
      rfl
    · rw [Category.assoc, hg]
      exact (pullback.condition_assoc f).symm
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U
  · intro h hh
    apply hom_ext I f hf h _ hh
    apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U

theorem isBlowup : IsBlowup I (projection I) :=
  ⟨projection_invertible I, fun _ f hf => universal I f hf⟩

end
end MaximalSeshadri.BlowupGluing

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry MaximalSeshadri.Geometry

lemma regular_map_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : IsRegular r) : IsRegular (f r) := by
  let :=  f.toAlgebra
  let : Module.Flat R S := hf
  apply (Commute.isRegular_iff (fun s => Commute.all _ s)).mpr
  change Function.Injective (fun s : S => f r * s)
  exact Module.Flat.isSMulRegular_of_isRegular hr

variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)

lemma invertible_flat_pullback (hf : InvertiblePullbackIdeal I f)
    (g : Z ⟶ Y) [Flat g] : InvertiblePullbackIdeal I (g ≫ f) := by
  apply invertible_of_local_equations
  intro z
  obtain ⟨U, hzU, r, hr, hI⟩ := local_equations hf (g z)
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ g ⁻¹ᵁ U.1 from hzU)
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.toScheme := hV
  let g' := g.resLE U.1 V hVU
  let : IsZariskiLocalAtSource (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  let : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  let : Flat g' := IsZariskiLocalAtSource.resLE hVU (inferInstanceAs (Flat g))
  have he : V.ι ≫ g = g' ≫ U.1.ι := (g.resLE_comp_ι hVU).symm
  refine ⟨⟨V, hV⟩, hzV, g'.appTop r,
    regular_map_flat g'.appTop.hom g'.flat_appTop hr, ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, ← Category.assoc, he,
    Category.assoc, Scheme.IdealSheafData.comap_comp,
    IdealPullback.comap_top, Scheme.IdealSheafData.comap_comp, hI,
    Ideal.map_span, Set.image_singleton]

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.flat_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X) [Flat j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_flat_pullback I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

lemma IsBlowup.flat_baseChangeSquare {B' : Scheme} (hπ : IsBlowup I π) (j : Z ⟶ X)
    [Flat j] (ρ : B' ⟶ Z) (hρ : IsBlowup (I.comap j) ρ)
    (β : B' ⟶ B) (hβ : β ≫ π = ρ ≫ j) : IsPullback ρ β j π := by
  let e := hρ.iso (hπ.flat_baseChange j)
  refine IsPullback.of_iso_pullback ⟨hβ.symm⟩ e
    (hρ.iso_hom_comp (hπ.flat_baseChange j)) ?_
  apply hπ.hom_ext (ρ ≫ j)
  · exact (InvertibleLocal.invertible_congr
      (Scheme.IdealSheafData.comap_comp I ρ j)).mpr hρ.1
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      hρ.iso_hom_comp (hπ.flat_baseChange j)]
  · exact hβ

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma generators_adjoin_of_span {ι : Type*} (a : ι → I)
    (ha : Ideal.span (Set.range fun i => (a i).val) = I) :
    Algebra.adjoin R (Set.range fun i => generator I (a i)) = ⊤ := by
  apply (Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  calc
    _ = Algebra.adjoin R
        (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
      conv_rhs => rw [← ha, Submodule.map_span, Algebra.adjoin_span]
      congr 1
      ext p
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨(a i).val, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨generator I (a i), ⟨i, rfl⟩, rfl⟩
    _ = reesAlgebra I := adjoin_monomial_eq_reesAlgebra I

lemma generators_adjoin_zero_of_span {ι : Type*} (a : ι → I)
    (ha : Ideal.span (Set.range fun i => (a i).val) = I) :
    Algebra.adjoin (piece I 0) (Set.range fun i => generator I (a i)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  have hh : p ∈ Algebra.adjoin R (Set.range fun i => generator I (a i)) := by
    rw [generators_adjoin_of_span I a ha]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) _).algebraMap_mem (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

lemma iSup_basicOpen_of_span {ι : Type*} (a : ι → I)
    (ha : Ideal.span (Set.range fun i => (a i).val) = I) :
    ⨆ i, Proj.basicOpen (piece I) (generator I (a i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (fun i => generator I (a i))
    (fun i => ⟨1, generator_mem I (a i)⟩) (generators_adjoin_zero_of_span I a ha)

def generatorCover {ι : Type u} (a : ι → I)
    (ha : Ideal.span (Set.range fun i => (a i).val) = I) :
    (affineBlowup I).AffineOpenCover where
  I₀ := ι
  X i := CommRingCat.of (chart I (a i))
  f i := (chartCover I).f (a i)
  map_prop i := (chartCover I).map_prop (a i)
  idx x := (Opens.mem_iSup.mp ((iSup_basicOpen_of_span I a ha).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (m := 1) (piece I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (Opens.mem_iSup.mp ((iSup_basicOpen_of_span I a ha).ge
      (Set.mem_univ x))).choose_spec

end
end MaximalSeshadri.ReesGrading


end

end OAI
