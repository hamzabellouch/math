import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.IntegralExtension

namespace OAI

section
noncomputable section
                                                
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma subscheme_chart_preimage_basicOpen {X : Scheme.{0}} (J : X.IdealSheafData)
    (U : X.affineOpens) (x : Γ(X, U.1)) :
    (J.subschemeCover.f U ≫ J.subschemeι) ⁻¹ᵁ X.basicOpen x =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (J.ideal U) x) := by
  rw [J.subschemeCover_map_subschemeι, J.glueDataObjι_ι]
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))) ≫
    U.2.fromSpec) ⁻¹ᵁ X.basicOpen x =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (J.ideal U) x)
  rw [Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_basicOpen]
  rfl

theorem integral_ideal_of_regular_chart {X : Scheme.{0}} [IsIntegral X]
    (J : X.IdealSheafData) (V : X.Opens) [IsIntegral (J.comap V.ι).subscheme]
    (U : X.affineOpens) [Nonempty U.1] (hcover : V ⊔ U.1 = ⊤)
    (r : Γ(X, U.1)) (hr : J.ideal U = Ideal.span {r})
    (x y : Γ(X, U.1)) (hx : x ≠ 0)
    (hxy : ∀ a, x ∣ y * a → x ∣ a)
    (hVx : X.basicOpen x ≤ V) (hVy : X.basicOpen y ≤ V) :
    IsIntegral J.subscheme := by
  let V' := J.subschemeι ⁻¹ᵁ V
  let e := restrictedIdealOpenIso J V
  let : IsIntegral V'.toScheme := IsIntegral.of_isIso e.hom
  refine @integral_of_principal_extension _ V' _ Γ(X, U.1) _ _
    (J.ideal U) r hr x y hx hxy (J.subschemeCover.f U)
    (J.subschemeCover.map_prop U) ?_ ?_ ?_
  · refine (congrArg (V' ⊔ ·) (J.opensRange_subschemeCover_map U)).trans ?_
    change (J.subschemeι ⁻¹ᵁ V) ⊔ (J.subschemeι ⁻¹ᵁ U.1) = ⊤
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  · rw [← subscheme_chart_preimage_basicOpen J U x, Scheme.Hom.comp_preimage]
    exact (J.subschemeCover.f U).preimage_mono (J.subschemeι.preimage_mono hVx)
  · rw [← subscheme_chart_preimage_basicOpen J U y, Scheme.Hom.comp_preimage]
    exact (J.subschemeCover.f U).preimage_mono (J.subschemeι.preimage_mono hVy)

end
end MaximalSeshadri.Hartogs
end


end
end

end OAI
