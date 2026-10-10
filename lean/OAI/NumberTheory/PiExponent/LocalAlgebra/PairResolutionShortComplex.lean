import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalUnmixedness

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalUnmixedness
open CategoryTheory

variable {S : Type*} [CommRing S]

def pairQuotientShortComplex (f g : S) : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk (Ideal.ofList [f, g]).subtype (Ideal.ofList [f, g]).mkQ
    (by
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero (Ideal.ofList [f, g])).mpr x.property)

def pairSyzygyShortComplex (f g : S) : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk (pairBoundary f g) (pairToIdeal f g) (by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change f * (-g * t) + g * (f * t) = 0
    ring)

theorem pairQuotientShortComplex_shortExact (f g : S) :
    (pairQuotientShortComplex f g).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact ideal_subtype_range_eq_quotient_kernel f g
  · exact (ModuleCat.mono_iff_injective _).mpr (Ideal.ofList [f, g]).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

theorem pairSyzygyShortComplex_shortExact (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    (pairSyzygyShortComplex f g).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact regular_pair_range_boundary_eq_kernel_toIdeal f g hreg
  · exact (ModuleCat.mono_iff_injective _).mpr (regular_pair_boundary_injective f g hreg)
  · exact (ModuleCat.epi_iff_surjective _).mpr (pairToIdeal_surjective f g)

theorem pair_resolution_shortComplex_link (f g : S) :
    (pairSyzygyShortComplex f g).X₃ = (pairQuotientShortComplex f g).X₁ := rfl

end PiExponentJets.PolynomialLocalUnmixedness

end

end OAI
