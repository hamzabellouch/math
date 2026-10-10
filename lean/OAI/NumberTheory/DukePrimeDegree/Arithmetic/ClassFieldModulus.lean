import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ClassFieldBridge

namespace OAI

/-!
# A common even modulus away from ramification

Enlarging the finite conductor to contain the discriminant primes leaves
its infinite part empty and its Artin-kernel property intact. An ordinary
positive integer then imposes all of its local congruences.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree

open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyReal L]

theorem exists_even_unramified_artin_modulus :
    ∃ m : RayClass.Modulus K, m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val := by
  obtain ⟨m, hm, hnorm⟩ := exists_even_artin_modulus K L
  let D : 𝓞 K := (NumberField.discr L).natAbs
  have hD : D ≠ 0 := by
    change ((NumberField.discr L).natAbs : 𝓞 K) ≠ 0
    exact_mod_cast (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)).ne'
  let I := integralIdealFractionalUnit (Ideal.span {D})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hD)
  let b : RayClass.FiniteModulus K :=
    (FractionalIdealGroup.countVector I).mapRange Int.natAbs rfl
  let m' := m.replaceFinitePart (m.finitePart + b)
  have hle : m ≤ m' := by
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact Finset.Subset.refl _
  refine ⟨m', hm, (RayClass.Modulus.congruenceSubgroup_antitone hle).trans hnorm, ?_⟩
  intro v hv
  have hv0 : m'.finitePart v = 0 := Finsupp.notMem_support_iff.mp hv
  have hb : b v = 0 := by
    change m.finitePart v + b v = 0 at hv0
    omega
  have hcount : FractionalIdeal.count K v (Ideal.span {D}) = 0 := by
    have hc : Int.natAbs (FractionalIdeal.count K v (Ideal.span {D})) = 0 := hb
    exact Int.natAbs_eq_zero.mp hc
  have hnot : D ∉ v.asIdeal := by
    exact mt ((principal_count_ne_zero_iff_mem K D hD v).mpr) (by simpa using hcount)
  let : (primeAbove K L v).val.IsPrime := (primeAbove K L v).property.1
  exact unramified_of_absDiscr_not_mem K L v.asIdeal (primeAbove K L v).val
    (primeAbove K L v).property.2.over.symm hnot

theorem exists_integer_even_artin_modulus :
    ∃ (m : RayClass.Modulus K) (N : ℕ), 0 < N ∧
      (NumberField.discr L).natAbs ∣ N ∧ m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range ∧
      (∀ v ∈ m.finitePart.support,
        algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m.finitePart v) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val := by
  obtain ⟨m, hm, hnorm, hur⟩ := exists_even_unramified_artin_modulus (K := K) (L := L)
  obtain ⟨N, hN, hdN, hlocal⟩ := exists_integer_for_local_congruences
    m.finitePart.support m.finitePart (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L))
  exact ⟨m, N, hN, hdN, hm, hnorm, hlocal, hur⟩

end DukePrimeDegree

end

end OAI
