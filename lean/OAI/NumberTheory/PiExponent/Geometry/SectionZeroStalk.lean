import OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.SectionZeroStalk


theorem stalkMap_ker_eq_map_affine_ker
    {X Y : Scheme} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (hU : IsAffineOpen U) (y : Y) (hy : f y ∈ U) :
    RingHom.ker (f.stalkMap y).hom =
      (RingHom.ker (f.app U).hom).map (X.presheaf.germ U (f y) hy).hom := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let q := hU.primeIdealOf ⟨f y, hy⟩
  let p := hV.primeIdealOf ⟨y, hy⟩
  let φ := (f.app U).hom
  let := X.presheaf.algebra_section_stalk ⟨f y, hy⟩
  let := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : V)
  let := hU.isLocalization_stalk ⟨f y, hy⟩
  let := hV.isLocalization_stalk ⟨y, hy⟩
  have hqp : p.asIdeal.comap φ = q.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hy (f := f)
    simpa only [V, Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal, φ, p, q] using congrArg PrimeSpectrum.asIdeal h
  have hmon : q.asIdeal.primeCompl.map φ = p.asIdeal.primeCompl := by
    simpa only [hqp] using p.asIdeal.map_primeCompl_comap_of_surjective φ (f.app_surjective U hU)
  have hf : (f.stalkMap y).hom =
      (IsLocalization.map (Y.presheaf.stalk y) φ
        (hmon.symm ▸ q.asIdeal.primeCompl.le_comap_map) : X.presheaf.stalk (f y) →+* Y.presheaf.stalk y) := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    exact Scheme.Hom.germ_stalkMap_apply f U y hy a
  rw [hf, IsLocalization.ker_map (Y.presheaf.stalk y) φ hmon]
  rfl

variable {X : Scheme.{0}}

theorem zero_stalk_kernel (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    RingHom.ker ((SectionZeroIdeal.zeroIdeal L s).subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U.1 _ hy)
        (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))} := by
  rw [stalkMap_ker_eq_map_affine_ker _ U.1 U.2 y hy,
    (SectionZeroIdeal.zeroIdeal L s).ker_subschemeι_app U,
    SectionZeroIdeal.zeroIdeal_on_frame L s U e,
    Ideal.map_span, Set.image_singleton]

def sectionGerm (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) : X.presheaf.stalk x :=
  (X.presheaf.germ U.1 x hx) (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))

def zeroStalkQuotientEquiv (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y) ⧸
      Ideal.span {sectionGerm L s U e _ hy}) ≃+*
      (SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y :=
  (Ideal.quotEquivOfEq (zero_stalk_kernel L s U e y hy).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((SectionZeroIdeal.zeroIdeal L s).subschemeι.stalkMap_surjective y))

theorem intrinsic_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm

theorem sectionGerm_ne_zero [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) : sectionGerm L s U e x hx ≠ 0 := by
  let : Nonempty U.1.toScheme := ⟨⟨x,hx⟩⟩
  intro h
  have hg : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) = 0 :=
    (map_eq_zero_iff _ (germ_injective_of_isIntegral X x hx)).mp h
  have hc : coefficient e (restrictSection U.1.ι s) = 0 :=
    (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective).mp hg
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  exact hc.trans ((congrArg (coefficient e)
    (restrictSection_zero (M := L.sheaf) U.1.ι)).trans (coefficient_zero e)).symm

theorem zero_stalk_length_eq_order [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1)
    [IsDiscreteValuationRing (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))] :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
      IsDiscreteValuationRing.addVal
        (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))
        (sectionGerm L s U e _ hy) := by
  let A := X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y)
  let c : A := sectionGerm L s U e _ hy
  have hlen := intrinsic_length_eq_of_ringEquiv (zeroStalkQuotientEquiv L s U e y hy)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  exact hlen.symm.trans (hsc.symm.trans
    (CurveLocalOrder.length_quotient_span_eq_addVal (sectionGerm_ne_zero L s hs U e _ hy)))

end PiExponent.SectionZeroStalk

end

end OAI
