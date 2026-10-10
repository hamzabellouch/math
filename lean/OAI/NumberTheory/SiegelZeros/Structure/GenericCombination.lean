import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span

namespace OAI

namespace SiegelZeros


namespace W20

variable {K M I J : Type*} [Field K] [Infinite K]
  [AddCommGroup M] [Module K M] [Finite I]

theorem exists_linearCombination_avoiding_submodules
    (g : J → M) (P : I → Submodule K M)
    (h : ∀ i, ¬ Submodule.span K (Set.range g) ≤ P i) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  let bad : I → Submodule K (J →₀ K) :=
    fun i => (P i).comap (Finsupp.linearCombination K g)
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i hi
    apply h i
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hc : Finsupp.single j (1 : K) ∈ bad i := by
      rw [hi]
      trivial
    change Finsupp.linearCombination K g (Finsupp.single j 1) ∈ P i at hc
    simpa using hc
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨c, hc⟩

variable {R : Type*} [CommRing R] [Algebra K R]

theorem exists_linearCombination_avoiding_ideals
    (g : J → R) (P : I → Ideal R)
    (h : ∀ i, ¬ Ideal.span (Set.range g) ≤ P i) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply exists_linearCombination_avoiding_submodules g
    (fun i => (P i).restrictScalars K)
  intro i hi
  apply h i
  apply Ideal.span_le.mpr
  intro x hx
  exact hi (Submodule.subset_span hx)

theorem exists_span_element_avoiding_ideals
    (g : J → R) (P : I → Ideal R)
    (h : ∀ i, ¬ Ideal.span (Set.range g) ≤ P i) :
    ∃ x ∈ Submodule.span K (Set.range g), ∀ i, x ∉ P i := by
  obtain ⟨c, hc⟩ := exists_linearCombination_avoiding_ideals (K := K) g P h
  refine ⟨Finsupp.linearCombination K g c, ?_, hc⟩
  rw [← Finsupp.range_linearCombination]
  exact ⟨c, rfl⟩

theorem exists_linearCombination_avoiding_primes_below_radical
    (g : J → R) (m : Ideal R)
    (hgen : (Ideal.span (Set.range g)).radical = m)
    (P : I → Ideal R) (hprime : ∀ i, (P i).IsPrime)
    (hbelow : ∀ i, P i < m) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply exists_linearCombination_avoiding_ideals g P
  intro i hle
  have hmle : m ≤ P i := by
    rw [← hgen]
    exact (hprime i).radical_le_iff.mpr hle
  exact (not_le_of_gt (hbelow i)) hmle

end W20


end SiegelZeros

end OAI
