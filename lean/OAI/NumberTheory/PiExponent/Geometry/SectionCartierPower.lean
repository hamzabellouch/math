import OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction
import OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference
import OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

theorem sectionZero_dimension_succ_le [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    [Nonempty (zeroIdeal L s).subscheme] :
    topologicalKrullDim (zeroIdeal L s).subscheme + 1 ≤ topologicalKrullDim X :=
  proper_closed_subscheme_dimension_succ_le (zeroIdeal L s).subschemeι
    (zeroIdeal_not_surjective L s hs)

theorem cartierPower_zeroIdeal_frames (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : (L.pow n).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : (L.pow (n+1)).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        (zeroIdeal L s).ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
            (cartierPowerMultiply L s n) ≫ e'.hom))} := by
  intro x
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let e := restrictOpenFrame hUV eV
  refine ⟨⟨U,hU⟩,hxU,modulePowFrame U e n,modulePowFrame U e (n+1),?_⟩
  exact (zeroIdeal_on_frame L s ⟨U, hU⟩ e).trans
    (cartierPowerMultiply_ideal L s n ⟨U, hU⟩ e).symm

theorem cartierPower_restriction_shortExact [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    ∃ hz : cartierPowerMultiply L s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1)) = 0,
      (ShortComplex.mk (cartierPowerMultiply L s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1))) hz).ShortExact := by
  exact @PiExponentSeshadri.CartierSequence.exact X p (L.pow n) (L.pow (n+1))
    (cartierPowerMultiply L s n) (cartierPowerMultiply_mono L s hs n)
    (zeroIdeal L s) (cartierPower_zeroIdeal_frames L s n)

def cartierPowerQuotientIso [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    cartierPowerQuotient L s n ≅
      (Scheme.Modules.pushforward (zeroIdeal L s).subschemeι).obj
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) := by
  let h := cartierPower_restriction_shortExact p L s hs n
  let hz := h.choose
  have hS := h.choose_spec
  letI := hS.epi_g
  exact (colimit.isColimit _).coconePointUniqueUpToIso hS.exact.gIsCokernel

theorem cartierPower_euler_difference [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n d : ℕ)
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
    (cartierPowerMultiply L s n) (cartierPowerMultiply_mono L s hs n) (zeroIdeal L s) (cartierPower_zeroIdeal_frames L s n) d hfiniteM hfiniteN
    hfiniteRestricted hzeroM hzeroRestricted

end
end PiExponent.NumericalAmpleness

end OAI
