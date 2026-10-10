import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import OAI.NumberTheory.PiExponent.LocalAlgebra.CyclicPrimeFactor

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem map_colon_singleton_localization
    (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (I : Ideal R) (f : R) :
    (I.colon {f}).map (algebraMap R L) =
      (I.map (algebraMap R L)).colon {algebraMap R L f} := by
  apply (IsLocalization.orderEmbedding S L).injective
  ext a
  change algebraMap R L a ∈ (I.colon {f}).map (algebraMap R L) ↔
    algebraMap R L a ∈ (I.map (algebraMap R L)).colon {algebraMap R L f}
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul,
    IsLocalization.algebraMap_mem_map_algebraMap_iff S L, mul_assoc]

noncomputable def localizedCyclicFactorEquiv
    (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (I : Ideal R) (f : R) :
    (L ⧸ (I.colon {f}).map (algebraMap R L)) ≃ₗ[L]
      (((I ⊔ Ideal.span {f}).map (algebraMap R L)) ⧸
        (I.map (algebraMap R L)).submoduleOf
          ((I ⊔ Ideal.span {f}).map (algebraMap R L))) := by
  rw [map_colon_singleton_localization S L, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton]
  exact cyclicFactorEquiv (I.map (algebraMap R L)) (algebraMap R L f)

noncomputable def primeLocalizedCyclicFactorEquiv
    (Q : Ideal R) [Q.IsPrime] (I : Ideal R) (f : R) :
    (Localization.AtPrime Q ⧸ (I.colon {f}).map
      (algebraMap R (Localization.AtPrime Q))) ≃ₗ[Localization.AtPrime Q]
      (((I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q))) ⧸
        (I.map (algebraMap R (Localization.AtPrime Q))).submoduleOf
          ((I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q)))) :=
  localizedCyclicFactorEquiv Q.primeCompl (Localization.AtPrime Q) I f

end PiExponentJets.W22

end OAI
