import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.NormNum

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W14

open scoped TensorProduct

theorem uniformizer_not_mem_maximalIdeal_sq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    π ∉ (IsLocalRing.maximalIdeal R) ^ 2 := by
  intro h
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hv := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h
  rw [hπ.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ] at hv
  norm_num at hv

theorem uniformizer_cotangent_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    (hmem : π ∈ IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal R).toCotangent ⟨π, hmem⟩ ≠ 0 := by
  rw [ne_eq, Ideal.toCotangent_eq_zero]
  exact uniformizer_not_mem_maximalIdeal_sq hπ

theorem smooth_conormal_tensor_ne_zero {k R S : Type*}
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R]
    [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k S]
    (hsurj : Function.Surjective (algebraMap R S))
    (x : RingHom.ker (algebraMap R S))
    (hx : (x : R) ∉ (RingHom.ker (algebraMap R S)) ^ 2) :
    (1 : S) ⊗ₜ[R] (KaehlerDifferential.D k R (x : R)) ≠ 0 := by
  obtain ⟨l, hl⟩ :=
    (Algebra.FormallySmooth.iff_split_injection (R := k) hsurj).mp
      (inferInstance : Algebra.FormallySmooth k S)
  have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor k R S) := by
    exact (show Function.LeftInverse l
      (KaehlerDifferential.kerCotangentToTensor k R S) from
      fun z => LinearMap.congr_fun hl z).injective
  intro hz
  apply hx
  apply (Ideal.toCotangent_eq_zero _ x).mp
  apply hinj
  rw [map_zero, KaehlerDifferential.kerCotangentToTensor_toCotangent]
  exact hz

end SiegelZerosAwei.Workers.W14

end

end SiegelZeros

end OAI
