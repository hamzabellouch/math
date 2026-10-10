import Mathlib

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace SpecMaps
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
  erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
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

end SpecMaps

namespace SchematicExt
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

end SchematicExt

end PiExponentSeshadri

end

end OAI
