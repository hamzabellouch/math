import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoefficientNaturalCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

namespace OAI

/-! # Short exact coefficient sequences in a projective-resolution Hom complex -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def resolutionCoefficientSequence (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (repCochainPostcomp ℤ P.complex S.f) (repCochainPostcomp ℤ P.complex S.g)
    (by
      ext i v
      change P.complex.X i ⟶ S.X₁ at v
      change (v ≫ S.f) ≫ S.g = 0
      rw [Category.assoc, S.zero, comp_zero])

theorem resolutionCoefficientSequence_shortExact
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (resolutionCoefficientSequence P S).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine {
    exact := ?_
    mono_f := ?_
    epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro v hv
    change P.complex.X i ⟶ S.X₂ at v
    change v ≫ S.g = 0 at hv
    exact ⟨hS.exact.lift v hv, hS.exact.lift_f v hv⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro v w hvw
    change P.complex.X i ⟶ S.X₁ at v w
    change v ≫ S.f = w ≫ S.f at hvw
    exact (cancel_mono S.f).mp hvw
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro v
    change P.complex.X i ⟶ S.X₃ at v
    exact ⟨Projective.factorThru v S.g, Projective.factorThru_comp v S.g⟩

end PolycyclicRecognition

end

end OAI
