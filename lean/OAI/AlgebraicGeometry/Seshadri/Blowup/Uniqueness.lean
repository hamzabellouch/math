import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.PrincipalCharts

namespace OAI

section
namespace MaximalSeshadri.SpecMaps
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

def coordinate (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

lemma coordinate_ext {f g : X ⟶ Spec R} (h : coordinate f = coordinate g) : f = g :=
  (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm.injective
    (Opposite.unop_injective h)

@[simp] lemma coordinate_comp (f : X ⟶ Y) (g : Y ⟶ Spec R) :
    coordinate (f ≫ g) = coordinate g ≫ f.appTop := by
  simp [coordinate]

@[simp] lemma coordinate_spec (f : R ⟶ S) : coordinate (Spec.map f) = f ≫ (Scheme.ΓSpecIso S).inv := by
  simp [coordinate]

@[simp] lemma coordinate_comp_spec (f : X ⟶ Spec S) (g : R ⟶ S) :
    coordinate (f ≫ Spec.map g) = g ≫ coordinate f := by
  simp [coordinate]

lemma factor (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map (coordinate f) = f := by
  unfold coordinate
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

lemma preimage_basicOpen (f : X ⟶ Spec R) (a : R) :
    f ⁻¹ᵁ PrimeSpectrum.basicOpen a = X.basicOpen (coordinate f a) := by
  conv_lhs => rw [← factor f]
  change X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (coordinate f a) = _
  exact Scheme.toSpecΓ_preimage_basicOpen _ _

lemma isUnit_of_basicOpen_eq_top (a : Γ(X, ⊤)) (h : X.basicOpen a = ⊤) : IsUnit a := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toLocallyRingedSpace.toRingedSpace ⊤ a
  intro x hx
  apply (Scheme.mem_basicOpen X a x hx).mp
  rw [h]
  trivial

lemma isUnit_coordinate_of_preimage_top (f : X ⟶ Spec R) (a : R)
    (h : f ⁻¹ᵁ PrimeSpectrum.basicOpen a = ⊤) : IsUnit (coordinate f a) := by
  apply isUnit_of_basicOpen_eq_top
  rwa [preimage_basicOpen] at h

lemma ideal_unit_generator (I : Ideal R) (f : X ⟶ Spec R)
    (hI : I.map (coordinate f).hom = ⊤) (x : X) :
    ∃ a : I, x ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val := by
  by_contra! hn
  have hle : I ≤ (f x).asIdeal := by
    intro a ha
    exact not_not.mp (hn ⟨a, ha⟩)
  have hmap : I.map (coordinate f).hom ≤ (X.toSpecΓ x).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hm := hle ha
    rw [← factor f, Scheme.Hom.comp_apply, Spec.map_apply] at hm
    exact hm
  rw [hI] at hmap
  exact (X.toSpecΓ x).isPrime.ne_top (top_unique hmap)

end
end MaximalSeshadri.SpecMaps

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

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
  let : IsOpenImmersion ((chartCover I).f a) := (chartCover I).map_prop a
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
  let g' : Y ⟶ Spec (CommRingCat.of (chart I a)) :=
    IsOpenImmersion.lift (X := Spec ((chartCover I).X a)) ((chartCover I).f a) g (hrange g hg)
  let h' : Y ⟶ Spec (CommRingCat.of (chart I a)) :=
    IsOpenImmersion.lift (X := Spec ((chartCover I).X a)) ((chartCover I).f a) h (hrange h hh)
  have hg' : g' ≫ (chartCover I).f a = g :=
    IsOpenImmersion.lift_fac ((chartCover I).f a) g (hrange g hg)
  have hh' : h' ≫ (chartCover I).f a = h :=
    IsOpenImmersion.lift_fac ((chartCover I).f a) h (hrange h hh)
  have eg : g' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    calc
      _ = g' ≫ ((chartCover I).f a ≫ projection I) :=
        congrArg (fun morphism => g' ≫ morphism) (chartCover_projection I a).symm
      _ = (g' ≫ (chartCover I).f a) ≫ projection I :=
        (Category.assoc g' ((chartCover I).f a) (projection I)).symm
      _ = f := (congrArg (fun morphism => morphism ≫ projection I) hg').trans hg
  have eh : h' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    calc
      _ = h' ≫ ((chartCover I).f a ≫ projection I) :=
        congrArg (fun morphism => h' ≫ morphism) (chartCover_projection I a).symm
      _ = (h' ≫ (chartCover I).f a) ≫ projection I :=
        (Category.assoc h' ((chartCover I).f a) (projection I)).symm
      _ = f := (congrArg (fun morphism => morphism ≫ projection I) hh').trans hh
  have he : coordinate g' (chartBase I a a.val) = coordinate f a.val := by
    have hc := congrArg coordinate eg
    rw [coordinate_comp_spec] at hc
    exact ConcreteCategory.congr_hom hc a.val
  have hgh := chart_scheme_ext I a g' h' (eg.trans eh.symm) (by rw [he]; exact hu.isRegular)
  rw [← hg', ← hh', hgh]

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.SchematicExt
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {W X Y Z : Scheme.{u}}

lemma ext_of_ker_eq_bot_of_isSeparated {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) (hι : ι.ker = ⊥) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  let l : U' ⟶ equalizer f' g' := equalizer.lift ι' (by ext1; exact hU)
  have hl : l.left ≫ (equalizer.ι f' g').left = ι := by
    change (l ≫ equalizer.ι f' g').left = ι
    exact congrArg (fun k : U' ⟶ X' => k.left) (equalizer.lift_ι ι' _)
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    apply bot_unique
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := l.left.le_ker_comp _
         _ = ⊥ := by rw [hl, hι]
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

lemma basicOpen_ker_eq_bot [IsAffine X] (r : Γ(X, ⊤)) (hr : IsRegular r) :
    (X.basicOpen r).ι.ker = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  apply bot_unique
  apply ((X.basicOpen r).ι.ideal_ker_le ⟨⊤, isAffineOpen_top X⟩).trans
  apply le_of_eq
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) :=
    IsLocalization.injective (Γ(X.basicOpen r, ⊤))
      (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))
  apply hinj
  change (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) x = 0 at hx
  simpa only [map_zero] using hx

end
end MaximalSeshadri.SchematicExt

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

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
    change U.ι ⁻¹ᵁ U = ⊤
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

end
end MaximalSeshadri.ReesGrading


end

end OAI
