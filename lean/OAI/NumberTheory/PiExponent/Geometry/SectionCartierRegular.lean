import OAI.NumberTheory.PiExponent.Geometry.SectionCartierPower

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

theorem cartierPowerMultiply_mono_of_mono (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

theorem regular_cartierPower_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    ∃ hz : cartierPowerMultiply L s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1)) = 0,
      (ShortComplex.mk (cartierPowerMultiply L s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1))) hz).ShortExact := by
  exact @PiExponentSeshadri.CartierSequence.exact X p (L.pow n) (L.pow (n+1))
    (cartierPowerMultiply L s n) (cartierPowerMultiply_mono_of_mono L s n)
    (zeroIdeal L s) (cartierPower_zeroIdeal_frames L s n)

def regular_cartierPowerQuotientIso
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    cartierPowerQuotient L s n ≅
      (Scheme.Modules.pushforward (zeroIdeal L s).subschemeι).obj
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) := by
  let h := regular_cartierPower_restriction_shortExact p L s n
  let hz := h.choose
  have hS := h.choose_spec
  letI := hS.epi_g
  exact (colimit.isColimit _).coconePointUniqueUpToIso hS.exact.gIsCokernel

theorem regular_cartierPower_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n d : ℕ)
    (hfiniteM : ∀ q ≤ d, letI := Module.compHom (cohomology (L.pow n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf q))
    (hfiniteN : ∀ q ≤ d, letI := Module.compHom (cohomology (L.pow (n+1)).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow (n+1)).sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) q)
        (baseScalars ((zeroIdeal L s).subschemeι ≫ p))
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) q))
    (hzeroM : ∀ z : cohomology (L.pow n).sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) d, z = 0) :
    eulerCharacteristic p d (L.pow (n+1)).sheaf - eulerCharacteristic p d (L.pow n).sheaf =
      eulerCharacteristic ((zeroIdeal L s).subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) := by
  exact @cartier_euler_difference X p (L.pow n) (L.pow (n+1))
    (cartierPowerMultiply L s n) (cartierPowerMultiply_mono_of_mono L s n) (zeroIdeal L s) (cartierPower_zeroIdeal_frames L s n) d hfiniteM hfiniteN
    hfiniteRestricted hzeroM hzeroRestricted

end
end PiExponent.NumericalAmpleness

end OAI
