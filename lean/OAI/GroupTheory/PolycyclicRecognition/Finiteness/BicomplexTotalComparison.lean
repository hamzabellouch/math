import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexTotalExactFunctor
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace OAI

/-! # Total comparison through an acyclic row kernel

The quotient in a short exact sequence of first-quadrant bicomplexes induces
a quasi-isomorphism of total complexes when the kernel rows are exact.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

theorem integral_shortExact_quasiIso_g {R : Type} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ)) (hS : S.ShortExact)
    (hz : ∀ n, IsZero (S.X₁.homology n)) : QuasiIso S.g := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let : Mono (homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g ((hz n).eq_of_src _ _)
  let : Epi S.g := hS.epi_g
  have : Epi (homologyMap S.g n) := by
    cases n with
    | zero =>
      exact epi_homologyMap_of_epi_of_not_rel S.g 0 (by
        intro j h
        change j + 1 = 0 at h
        omega)
    | succ n =>
      exact (hS.homology_exact₃ (n + 1) n rfl).epi_f ((hz n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

theorem bicomplex_total_quotient_quasiIso (S : ShortComplex NatBicomplex)
    (hS : S.ShortExact) (hex : ∀ i j, (S.X₁.X i).ExactAt j) :
    QuasiIso (HomologicalComplex₂.total.map S.g (ComplexShape.down ℕ)) := by
  let : PreservesFiniteLimits integralFirstQuadrantTotal :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits integralFirstQuadrantTotal :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact integral_shortExact_quasiIso_g (S.map integralFirstQuadrantTotal)
    (hS.map_of_exact integralFirstQuadrantTotal)
    (bicomplex_total_homology_isZero S.X₁ hex)

theorem bicomplex_total_of_row_epi_quasiIso {K L : NatBicomplex} (f : K ⟶ L)
    (hepi : ∀ i, Epi (f.f i)) (hquasi : ∀ i, QuasiIso (f.f i)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) := by
  let S : ShortComplex NatBicomplex :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let : Epi f := HomologicalComplex.epi_of_epi_f f hepi
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel f }
  apply bicomplex_total_quotient_quasiIso S hS
  intro i j
  have hSi := hS.map (HomologicalComplex.eval _ _ i)
  exact hSi.acyclic_X₁ (hquasi i) j

end PolycyclicRecognition

end

end OAI
