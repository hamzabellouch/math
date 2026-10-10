import OAI.GroupTheory.PolycyclicRecognition.Algebra.TwistedBilateralDifference
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI

/-! # Exactness and cokernel of the twisted bilateral difference -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

theorem twistedBilateralDifference_sum (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    twistedBilateralSum k M e (twistedBilateralDifference k M e f) = 0 := by
  have hm : twistedBilateralDifference k M e f ∈
      LinearMap.range (twistedBilateralDifference k M e) := ⟨f, rfl⟩
  rw [← twistedBilateralSum_ker_eq_range] at hm
  exact hm

def twistedBilateralSequence (e : M ≃ₗ[k] M) : ShortComplex (ModuleCat k) :=
  ShortComplex.mk (ModuleCat.ofHom (twistedBilateralDifference k M e))
    (ModuleCat.ofHom (twistedBilateralSum k M e)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact twistedBilateralDifference_sum k M e f)

theorem twistedBilateralSequence_shortExact (e : M ≃ₗ[k] M) :
    (twistedBilateralSequence k M e).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (twistedBilateralSum_ker_eq_range k M e).symm
  mono_f := (ModuleCat.mono_iff_injective _).mpr (twistedBilateralDifference_injective k M e)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (twistedBilateralSum_surjective k M e)

def twistedBilateralCokernelIso (e : M ≃ₗ[k] M) :
    cokernel (ModuleCat.ofHom (twistedBilateralDifference k M e)) ≅ ModuleCat.of k M :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (twistedBilateralSequence_shortExact k M e).gIsCokernel

end PolycyclicRecognition

end

end OAI
