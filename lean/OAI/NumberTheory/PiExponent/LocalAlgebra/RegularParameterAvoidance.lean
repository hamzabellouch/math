import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity

namespace OAI

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem isSMulRegular_of_avoids_associatedPrimes
    (M : Type*) [AddCommGroup M] [Module R M] (x : R)
    (hx : ∀ P : Ideal R, IsAssociatedPrime P M → x ∉ P) :
    IsSMulRegular M x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hy
  by_contra hne
  have hzero : x ∈ {r : R | ∃ z : M, z ≠ 0 ∧ r • z = 0} := ⟨y, hne, hy⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors R M] at hzero
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hzero
  exact hx P hP hxP

variable [IsLocalRing R]

omit [IsNoetherianRing R] in
theorem regular_append_singleton_of_quotient_smulRegular
    (rs : List R) (hreg : IsRegular R rs) (x : R)
    (hx : x ∈ maximalIdeal R)
    (hregular : IsSMulRegular (R ⧸ Ideal.ofList rs) x) :
    IsRegular R (rs ++ [x]) := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := R) (rs := rs ++ [x]) ?_).mpr
  · apply (isWeaklyRegular_append_iff R rs [x]).mpr
    refine ⟨hreg.toIsWeaklyRegular, ?_⟩
    have heq : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
      (Ideal.ofList rs).mul_top
    rw [heq, isWeaklyRegular_singleton_iff]
    exact hregular
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (le_maximalIdeal (PiExponentSiegel.W20.regular_sequence_ideal_ne_top rs hreg))
        (Ideal.subset_span hy)
    · have heq : y = x := List.mem_singleton.mp hy
      simpa only [heq] using hx

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

theorem exists_constant_regular_extension
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (rs : List R) (hreg : IsRegular R rs)
    (hnot : ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ c : J →₀ k,
      Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) ∧
      IsRegular R (rs ++ [Finsupp.linearCombination k generators c]) := by
  classical
  let ass := associatedPrimes R (R ⧸ Ideal.ofList rs)
  let : Fintype ass := (associatedPrimes.finite R (R ⧸ Ideal.ofList rs)).fintype
  have hbelow (P : ass) : P.val < maximalIdeal R := by
    refine lt_iff_le_and_ne.mpr ⟨le_maximalIdeal P.property.isPrime.ne_top, ?_⟩
    intro heq
    exact hnot (heq ▸ P.property)
  obtain ⟨c, hc⟩ := PiExponentSiegel.W20.exists_linearCombination_avoiding_primes_below_radical
    (K := k) generators (maximalIdeal R) hrad (fun P : ass => P.val)
    (fun P => P.property.isPrime) hbelow
  have hlin : Finsupp.linearCombination k generators c ∈
      Submodule.span k (Set.range generators) := by
    rw [← Finsupp.range_linearCombination]
    exact ⟨c, rfl⟩
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k := by
    apply Submodule.span_le.mpr
    exact fun _ h => Ideal.subset_span h
  have hin : Finsupp.linearCombination k generators c ∈
      Ideal.span (Set.range generators) := hspan hlin
  refine ⟨c, hin, regular_append_singleton_of_quotient_smulRegular rs hreg _ ?_ ?_⟩
  · rw [← hrad]
    exact Ideal.le_radical hin
  · apply isSMulRegular_of_avoids_associatedPrimes
    intro P hP
    exact hc ⟨P, hP⟩

end PiExponentSiegel.W58

end

end OAI
