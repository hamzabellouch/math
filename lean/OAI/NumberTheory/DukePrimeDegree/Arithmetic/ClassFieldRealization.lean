import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ClassFieldModulus

namespace OAI

/-!
# Unconditional even ray realization of cyclic ideal characters

The conductor of a totally real cyclic extension has no infinite part.
Arithmetic Artin reciprocity and the common rational congruence modulus
therefore supply the kernel law for every actual Frobenius ideal
character. This gives their realization as even ray characters.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem idealCharacter_kernelLaw_of_even_modulus
    (m : RayClass.Modulus K) (hm : m.infinitePart = ∅)
    (hnorm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range)
    (hunram : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∉ m.finitePart.support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (N : ℕ)
    (hN : ∀ v ∈ m.finitePart.support,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m.finitePart v)
    (χ : (L ≃ₐ[K] L) →* ℂˣ) : PrincipalRay.KernelLaw (idealHom K L χ) N := by
  intro a ha hcong
  let x : Kˣ := Units.mk0 (a : K) (by exact_mod_cast ha)
  have hx : IdeleGroup.principalIdele K x ∈ RayClass.idelePrimeToModulusSubgroup m :=
    principalIdele_mem_even_ray_of_congruence m hm N hN a ha hcong
  let y : RayClass.idelePrimeToModulusSubgroup m := ⟨IdeleGroup.principalIdele K x, hx⟩
  let I := RayClass.primeToIdealMap m y
  have hI : I ∈ RayClass.principalRayIdealSubgroup m := by
    refine ⟨y, ?_, rfl⟩
    exact ⟨x, rfl⟩
  have H := idealCharacter_principalRay_eq_one m hnorm hunram χ I hI
  have hval : (I : FractionalIdealGroup K) = integralIdealFractionalUnit
      (Ideal.span {a}) (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha) := by
    change IdeleGroup.fractionalIdeal (IdeleGroup.principalIdele K x) = _
    rw [IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.coeIdeal_span_singleton a).symm
  change idealHom K L χ (I : FractionalIdealGroup K) = 1 at H
  change idealHom K L χ (integralIdealFractionalUnit (Ideal.span {a}) _) = 1
  rwa [hval] at H

end DukePrimeDegree

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

/-- Actual cyclic Frobenius characters of a totally real extension have
one common even ray modulus, with the discriminant primes removed. -/
theorem exists_cyclic_ray_family_unconditional
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] [NumberField.IsTotallyReal K] [NumberField.IsTotallyReal L] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr L).natAbs ∣ N ∧
      ∃ ψ : ((L ≃ₐ[K] L) →* ℂˣ) → EvenRayCharacter K N,
        (∀ χ, (ψ χ).idealHom = idealHom K L χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  let : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
  let : IsAbelianGalois K L := { is_comm.comm := mul_comm }
  obtain ⟨m, N, hN, hdN, hm, hnorm, hlocal, hur⟩ :=
    exists_integer_even_artin_modulus (K := K) (L := L)
  obtain ⟨ψ, hid, hψ⟩ := exists_cyclic_ray_family K L N hN
    (idealCharacter_kernelLaw_of_even_modulus m hm hnorm hur N hlocal)
  exact ⟨N, hN, hdN, ψ, hid, hψ⟩

end DukePrimeDegree

end

end OAI
