import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.HyperplaneIdeal
import OAI.AlgebraicGeometry.Seshadri.Blowup.PlaneCharts

namespace OAI

section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X Y B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma invertible_top (f : Y ⟶ X) : InvertiblePullbackIdeal ⊤ f := by
  apply InvertibleLocal.invertible_of_local_equations
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  refine ⟨⟨U, hU⟩, hyU, 1, isRegular_one, ?_⟩
  simp

lemma isBlowup_id (hI : InvertiblePullbackIdeal I (𝟙 X)) :
    IsBlowup I (𝟙 X) := by
  refine ⟨hI, fun Y f _ => ⟨f, by simp, ?_⟩⟩
  intro g hg
  simpa using hg

lemma IsBlowup.isIso_of_invertible (hπ : IsBlowup I π)
    (hI : InvertiblePullbackIdeal I (𝟙 X)) : IsIso π := by
  have hπe : (hπ.iso (isBlowup_id hI)).hom = π := by
    simpa using hπ.iso_hom_comp (isBlowup_id hI)
  rw [← hπe]
  infer_instance

lemma IsBlowup.isIso_over_complement (hπ : IsBlowup I π) :
    IsIso (pullback.fst (Scheme.Opens.ι (X := X) I.support.compl) π) := by
  apply (hπ.open_baseChange (Scheme.Opens.ι (X := X) I.support.compl)).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem smooth_point_blowup
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K)
    {B : Scheme} (π : B ⟶ Spec (.of S))
    (hπ : IsBlowup (IdealPullback.specIdeal (RingHom.ker ρ)) π) :
    SmoothOfRelativeDimension 2
      (π ≫ Spec.map (CommRingCat.ofHom (algebraMap K S))) := by
  obtain ⟨s, hs, hsm⟩ := exists_smooth_point_blowup_neighborhood ρ π hπ
  let I := IdealPullback.specIdeal (RingHom.ker ρ)
  let U : (Spec (.of S)).Opens := I.support.compl
  let a := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))
  let base := Spec.map (CommRingCat.ofHom (algebraMap K S))
  have hb : SmoothOfRelativeDimension 2 base := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mpr
    exact RingHom.locally_of
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2)) _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 2).mpr inferInstance)
  let obj : Bool → Scheme := fun b => if b then U.toScheme else Spec (.of (Localization.Away s))
  let map : (b : Bool) → obj b ⟶ Spec (.of S) := fun b =>
    Bool.rec a U.ι b
  have cover : ∀ p : Spec (.of S), ∃ b y, map b y = p := by
    intro p
    by_cases hp : p ∈ (I.support : Set (Spec (.of S)))
    · have hq : RingHom.ker ρ ≤ p.asIdeal := by
        rw [show (I.support : Set (Spec (.of S))) = PrimeSpectrum.zeroLocus (RingHom.ker ρ)
          from IdealPullback.specIdeal_support _] at hp
        exact (PrimeSpectrum.mem_zeroLocus p _).mp hp
      have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
        (fun c => ⟨algebraMap K S c, by simp⟩)
      have heq : p.asIdeal = RingHom.ker ρ :=
        (hmax.eq_of_le p.isPrime.ne_top hq).symm
      have hm : s ∉ p.asIdeal := by simpa only [heq, RingHom.mem_ker] using hs
      have hr := (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s)
      have hp' : p ∈ Set.range a := by
        change p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away s)))
        rw [hr]
        exact hm
      obtain ⟨y, hy⟩ := hp'
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨p, hp⟩ : U), rfl⟩
  let C : (Spec (.of S)).OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (C.pullback₁ π)
  intro b
  cases b
  · change SmoothOfRelativeDimension 2 (pullback.fst π a ≫ π ≫ base)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    have hc : a ≫ base =
        Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s))) := by
      rw [← Spec.map_comp]
      rfl
    rw [hc]
    have hsp : (pullbackSymmetry π a).hom ≫ pullback.fst a π = pullback.snd π a :=
      pullbackSymmetry_hom_comp_fst π a
    rw [← hsp, Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  · change SmoothOfRelativeDimension 2 (pullback.fst π U.ι ≫ π ≫ base)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    let := hπ.isIso_over_complement
    have : IsIso (pullback.snd π U.ι) := by
      rw [← pullbackSymmetry_hom_comp_fst π U.ι]
      infer_instance
    have : SmoothOfRelativeDimension 2 (U.ι ≫ base) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.PointBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S]
lemma specMap_ker (f : R →+* S) :
    (Spec.map (CommRingCat.ofHom f)).ker = specIdeal (RingHom.ker f) := by
  rw [Scheme.ker_of_isAffine, specIdeal]
  congr 1
  apply Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)]
  ext r
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  have he := CategoryTheory.congr_fun
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r
  change (Scheme.ΓSpecIso (.of S)).inv (f r) =
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) at he
  rw [← he]
  exact map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).inv).1

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme}

theorem smooth_rational_point_blowup (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 2 f] (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (π : B ⟶ X) (hπ : IsBlowup p.ker π) :
    SmoothOfRelativeDimension 2 (π ≫ f) := by
  let point : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  let := isClosedImmersion_of_comp_eq_id f p hp
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 2) (f := f) (p point)
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f (p point) := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst U
  let A := Γ(X, V)
  let g : CommRingCat.of K ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V e
  have hng : RingHom.IsStandardSmoothOfRelativeDimension 2 g.hom := by
    let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
      RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    rfl
  algebraize [g.hom]
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K A := hng.toAlgebra
  let j := hV.fromSpec
  have hmap : Spec.map g = j ≫ f := by
    dsimp only [g]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  have hps : Set.range p ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rw [show z = point from Subsingleton.elim _ _]
    rwa [hV.range_fromSpec]
  let l := IsOpenImmersion.lift j p hps
  have hlj : l ≫ j = p := IsOpenImmersion.lift_fac j p hps
  let q := Spec.preimage l
  have hq : Spec.map q = l := Spec.map_preimage l
  have hqg : g ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hmap, ← Category.assoc, hlj, hp, Spec.map_id]
  let ρ : A →ₐ[K] K :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hqg c }
  have hker : p.ker.comap j = IdealPullback.specIdeal (RingHom.ker ρ) := by
    have sq := IsOpenImmersion.isPullback_lift_id p j hps
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion p j,
      ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
      sq.isoPullback_hom_fst]
    change l.ker = _
    rw [← hq]
    exact IdealPullback.specMap_ker q.hom
  have hs : SmoothOfRelativeDimension 2 (pullback.fst j π ≫ j ≫ f) := by
    rw [← hmap]
    exact smooth_point_blowup ρ _ (by simpa only [hker] using hπ.flat_baseChange j)
  let W : X.Opens := p.ker.support.compl
  let obj : Bool → Scheme := fun b => if b then W.toScheme else Spec A
  let map : (b : Bool) → obj b ⟶ X := fun b => Bool.rec j W.ι b
  have cover : ∀ x : X, ∃ b y, map b y = x := by
    intro x
    by_cases hx : x ∈ (p.ker.support : Set X)
    · rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq] at hx
      obtain ⟨y, hy⟩ := hps hx
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨x, hx⟩ : W), rfl⟩
  let C : X.OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (C.pullback₁ π)
  intro b
  cases b
  · change SmoothOfRelativeDimension 2 (pullback.fst π j ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc,
      ← pullbackSymmetry_hom_comp_fst π j, Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  · change SmoothOfRelativeDimension 2 (pullback.fst π W.ι ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    let := hπ.isIso_over_complement
    have : IsIso (pullback.snd π W.ι) := by
      rw [← pullbackSymmetry_hom_comp_fst π W.ι]
      infer_instance
    have : SmoothOfRelativeDimension 2 (W.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.PointBlowup


end

end OAI
