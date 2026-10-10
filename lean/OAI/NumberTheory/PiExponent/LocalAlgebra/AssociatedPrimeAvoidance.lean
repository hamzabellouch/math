import Mathlib

namespace OAI

namespace PiExponent.GeometrySupport.AssociatedPrimeAvoidance
noncomputable section
open scoped BigOperators

theorem exists_regular_combination
    {K ι J : Type*} [Field K] [Infinite K] [Finite ι] [Fintype J]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, IsNoetherianRing (R i)] (a : ∀ i, J → R i)
    (hspan : ∀ i, Ideal.span (Set.range (a i)) = ⊤) :
    ∃ c : J → K, ∀ i, (∑ j, c j • a i j) ∈ nonZeroDivisors (R i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Fintype (associatedPrimes (R i) (R i)) :=
    (associatedPrimes.finite (R i) (R i)).fintype
  let B := (i : ι) × associatedPrimes (R i) (R i)
  let L (i : ι) : (J → K) →ₗ[K] R i := Fintype.linearCombination K (a i)
  let bad (b : B) : Submodule K (J → K) :=
    (b.2.val.restrictScalars K).comap (L b.1)
  have hbad : ∀ b : B, bad b ≠ ⊤ := by
    intro b hb
    apply b.2.property.isPrime.ne_top
    apply top_unique
    rw [← hspan b.1]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hm : Pi.single j (1 : K) ∈ bad b := by
      rw [hb]
      trivial
    change Fintype.linearCombination K (a b.1) (Pi.single j 1) ∈ b.2.val at hm
    rw [Fintype.linearCombination_apply_single, one_smul] at hm
    exact hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨c, fun i => ?_⟩
  by_contra hn
  have hz : (∑ j, c j • a i j) ∈ (nonZeroDivisors (R i) : Set (R i))ᶜ := hn
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors (R i)] at hz
  obtain ⟨P, hP, hmem⟩ := Set.mem_iUnion₂.mp hz
  apply hc ⟨i, ⟨P, hP⟩⟩
  change (∑ j, c j • a i j) ∈ P
  exact hmem

end
end PiExponent.GeometrySupport.AssociatedPrimeAvoidance

end OAI
