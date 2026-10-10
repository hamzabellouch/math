import OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt
import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

lemma base_pow_mul_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartBase I a (a.val ^ n) *
        HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp =
      chartBase I a (evaluation I p) := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_base, chartMap_mk]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I p) ⟨a.val ^ n, n, rfl⟩

end PiExponentSeshadri.ReesGrading

namespace PiExponentSeshadri.ProjBase
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma basicOpenToSpec_eq (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

lemma basicOpenToSpec_mem (f : A) (x : Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((Proj.basicOpenToSpec 𝒜 f) x).asIdeal ↔
      z.num.val ∈ x.val.asHomogeneousIdeal := by
  have he := congr($(basicOpenToSpec_eq 𝒜 f).base x)
  change (Proj.basicOpenToSpec 𝒜 f) x = (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x at he
  rw [he]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z

lemma toSpecZero_mem (x : Proj 𝒜) (a : 𝒜 0) :
    a ∈ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∈ x.asHomogeneousIdeal := by
  simp only [Proj.toSpecZero, Scheme.Hom.comp_apply, Spec.map_apply]
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a ∈
    ((Proj.basicOpenToSpec 𝒜 1) _).asIdeal ↔ _
  rw [show HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a =
    HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩ from rfl]
  erw [basicOpenToSpec_mem]
  change a.val ∈ ((Proj.basicOpen 𝒜 (1 : A)).ι
    (((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ((Proj 𝒜).topIso.inv x))).asHomogeneousIdeal ↔ _
  rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι, ← Scheme.Hom.comp_apply]
  rw [Scheme.toIso_inv_ι]; rfl

lemma toSpecZero_preimage (a : 𝒜 0) :
    Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen a = Proj.basicOpen 𝒜 a.val := by
  ext x
  change a ∉ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∉ x.asHomogeneousIdeal
  exact not_congr (toSpecZero_mem 𝒜 x a)

end PiExponentSeshadri.ProjBase

namespace PiExponentSeshadri.ReesGrading
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance projection_separated : IsSeparated (projection I) := by
  have hP : IsSeparated (Proj.toSpecZero (piece I)) := inferInstance
  have hQ : IsSeparated (Spec.map (zeroIso I).hom) := inferInstance
  exact MorphismProperty.comp_mem (@IsSeparated) _ _ hP hQ

lemma projection_mem (x : affineBlowup I) (s : R) :
    s ∈ ((projection I) x).asIdeal ↔
      algebraMap R (reesAlgebra I) s ∈ x.asHomogeneousIdeal := by
  change zeroEquiv I s ∈ ((Proj.toSpecZero (piece I)) x).asIdeal ↔ _
  exact ProjBase.toSpecZero_mem (piece I) x (zeroEquiv I s)

lemma projection_preimage (s : R) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen s =
      Proj.basicOpen (piece I) (algebraMap R (reesAlgebra I) s) := by
  ext x
  exact not_congr (projection_mem I x s)

lemma base_generator_comm (a b : I) :
    algebraMap R (reesAlgebra I) a.val * generator I b =
      algebraMap R (reesAlgebra I) b.val * generator I a := by
  apply Subtype.ext
  change C a.val * monomial 1 b.val = C b.val * monomial 1 a.val
  simp only [C_mul_monomial, mul_comm a.val b.val]

lemma projection_preimage_le_chart (a : I) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a.val ≤
      Proj.basicOpen (piece I) (generator I a) := by
  rw [projection_preimage]
  intro x hx
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))
  have h : x ∈ Proj.basicOpen (piece I)
      (algebraMap R (reesAlgebra I) a.val * generator I b) := by
    rw [Proj.basicOpen_mul]
    exact ⟨hx, hb⟩
  rw [base_generator_comm, Proj.basicOpen_mul] at h
  exact h.2

lemma chartHom_ext {S : Type*} [CommRing S] (a : I)
    (g h : chart I a →+* S) (he : g.comp (chartBase I a) = h.comp (chartBase I a))
    (hr : IsRegular (g (chartBase I a a.val))) : g = h := by
  have hb (s : R) : g (chartBase I a s) = h (chartBase I a s) := RingHom.congr_fun he s
  ext x
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  apply (hr.pow n).left
  have h₁ := congrArg g (base_pow_mul_mk I a n p hp)
  have h₂ := congrArg h (base_pow_mul_mk I a n p hp)
  simpa only [map_mul, map_pow, hb] using h₁.trans ((hb ((evaluation I) p)).trans h₂.symm)

open SpecMaps

lemma chart_scheme_ext {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ Spec (CommRingCat.of (chart I a)))
    (he : g ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) =
      h ≫ Spec.map (CommRingCat.ofHom (chartBase I a)))
    (hr : IsRegular (coordinate g (chartBase I a a.val))) : g = h := by
  apply coordinate_ext
  apply CommRingCat.hom_ext
  apply chartHom_ext I a _ _ _ hr
  have hc := congrArg coordinate he
  simp only [coordinate_comp_spec] at hc
  exact congrArg CommRingCat.Hom.hom hc

lemma ext_of_unit_generator {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hu : IsUnit (coordinate f a.val)) : g = h := by
  let hOpen : IsOpenImmersion ((chartCover I).f a) := (chartCover I).map_prop a
  have ht : f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val = ⊤ := by
    rw [preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
  have hrange (k : Y ⟶ affineBlowup I) (hk : k ≫ projection I = f) :
      Set.range k ⊆ Set.range ((chartCover I).f a) := by
    rintro _ ⟨y, rfl⟩
    change k y ∈ ((chartCover I).f a).opensRange
    change k y ∈ (Proj.awayι (piece I) (generator I a) (generator_mem I a)
      (show 0 < (1 : ℕ) from Nat.zero_lt_one)).opensRange
    rw [Proj.opensRange_awayι]
    apply projection_preimage_le_chart I a
    change (projection I) (k y) ∈ PrimeSpectrum.basicOpen a.val
    rw [← Scheme.Hom.comp_apply, hk]
    exact ht.ge (Set.mem_univ y)
  let g' : Y ⟶ Spec (CommRingCat.of (chart I a)) := @IsOpenImmersion.lift _ _ _ ((chartCover I).f a) g hOpen (hrange g hg)
  let h' : Y ⟶ Spec (CommRingCat.of (chart I a)) := @IsOpenImmersion.lift _ _ _ ((chartCover I).f a) h hOpen (hrange h hh)
  have hg' : g' ≫ (chartCover I).f a = g :=
    @IsOpenImmersion.lift_fac _ _ _ ((chartCover I).f a) g hOpen (hrange g hg)
  have hh' : h' ≫ (chartCover I).f a = h :=
    @IsOpenImmersion.lift_fac _ _ _ ((chartCover I).f a) h hOpen (hrange h hh)
  have eg : g' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    exact (congrArg (fun q : Spec (CommRingCat.of (chart I a)) ⟶ Spec (CommRingCat.of R) =>
      g' ≫ q) (chartCover_projection I a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Y ⟶ affineBlowup I => q ≫ projection I) hg').trans hg))
  have eh : h' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    exact (congrArg (fun q : Spec (CommRingCat.of (chart I a)) ⟶ Spec (CommRingCat.of R) =>
      h' ≫ q) (chartCover_projection I a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Y ⟶ affineBlowup I => q ≫ projection I) hh').trans hh))
  have he : coordinate g' (chartBase I a a.val) = coordinate f a.val := by
    have hc := congrArg coordinate eg
    rw [coordinate_comp_spec] at hc
    exact ConcreteCategory.congr_hom hc a.val
  have hgh := chart_scheme_ext I a g' h' (eg.trans eh.symm) (by rw [he]; exact hu.isRegular)
  rw [← hg', ← hh', hgh]


lemma ext_on_generator_open {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ g =
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ h := by
  let U : Y.Opens := f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val
  apply ext_of_unit_generator I a _ _ (U.ι ≫ f)
  · rw [Category.assoc, hg]
  · rw [Category.assoc, hh]
  · apply isUnit_coordinate_of_preimage_top
    erw [Scheme.Hom.comp_preimage]
    exact U.ι_preimage_self

lemma ext_of_unit_ideal {Y : Scheme.{u}}
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hI : I.map (coordinate f).hom = ⊤) : g = h := by
  refine Scheme.hom_ext_of_forall g h ?_
  intro y
  have ha : ∃ a : I, y ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val :=
    ideal_unit_generator (R := CommRingCat.of R) I f hI y
  obtain ⟨a, hay⟩ := ha
  refine ⟨f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val, hay, ?_⟩
  exact ext_on_generator_open I a g h f hg hh

lemma principal_basicOpen_unit_ideal {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) :
    I.map (coordinate ((Y.basicOpen r).ι ≫ f)).hom = ⊤ := by
  rw [coordinate_comp]
  change I.map ((Y.basicOpen r).ι.appTop.hom.comp (coordinate f).hom) = ⊤
  rw [← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen_top]
  exact (Y.basicOpen r).ι_preimage_self

lemma principal_unique {Y : Scheme.{u}} [IsAffine Y]
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) (hr : IsRegular r) :
    g = h := by
  apply SchematicExt.ext_of_ker_eq_bot_of_isSeparated (projection I) (hg.trans hh.symm)
    (Y.basicOpen r).ι (SchematicExt.basicOpen_ker_eq_bot r hr)
  exact ext_of_unit_ideal I _ _ ((Y.basicOpen r).ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh])
    (principal_basicOpen_unit_ideal I f r hI)

end PiExponentSeshadri.ReesGrading

end

end OAI
