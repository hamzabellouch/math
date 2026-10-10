import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiltrationLength

namespace OAI

namespace PiExponentJets.W22

open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

theorem map_ideal_eq_top_of_not_le
    (P Q : Ideal R) [Q.IsPrime] (hPQ : ¬ P ≤ Q) :
    P.map (algebraMap R (Localization.AtPrime Q)) = ⊤ := by
  obtain ⟨x, hxP, hxQ⟩ := SetLike.not_le_iff_exists.mp hPQ
  have hu : IsUnit (algebraMap R (Localization.AtPrime Q) x) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q x).mpr hxQ
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxP) hu

theorem localized_prime_factor_length_zero
    (P Q : Ideal R) [Q.IsPrime] (hPQ : ¬ P ≤ Q) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ P.map (algebraMap R (Localization.AtPrime Q))) = 0 := by
  rw [map_ideal_eq_top_of_not_le P Q hPQ]
  exact Module.length_eq_zero

theorem localized_prime_factor_length_one
    (Q : Ideal R) [Q.IsPrime] :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ Q.map (algebraMap R (Localization.AtPrime Q))) = 1 := by
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  let : IsSimpleModule (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact Module.length_eq_one _ _

theorem prime_not_le_of_ne_minimal
    (I P Q : Ideal R) [P.IsPrime]
    (hQ : Q ∈ I.minimalPrimes) (hIP : I ≤ P) (hne : P ≠ Q) : ¬ P ≤ Q := by
  intro hPQ
  exact hne (le_antisymm hPQ (hQ.2 ⟨inferInstance, hIP⟩ hPQ))

theorem localized_prime_factor_length
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hQ : Q ∈ I.minimalPrimes) (hIP : I ≤ P) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ P.map (algebraMap R (Localization.AtPrime Q))) =
      if P = Q then 1 else 0 := by
  classical
  by_cases hPQ : P = Q
  · subst P
    simpa only [ite_true] using localized_prime_factor_length_one Q
  · rw [ite_eq_right hPQ]
    exact localized_prime_factor_length_zero P Q
      (prime_not_le_of_ne_minimal I P Q hQ hIP hPQ)

theorem local_component_length_eq_prime_factor_count
    (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
    (N : ℕ → Submodule (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))))
    (hmono : ∀ i, N i ≤ N (i + 1)) (hzero : N 0 = ⊥)
    (n : ℕ) (htop : N n = ⊤)
    (P : ℕ → Ideal R) [∀ i, (P i).IsPrime]
    (hIP : ∀ i < n, I ≤ P i)
    (e : ∀ i < n,
      (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) ≃ₗ[Localization.AtPrime Q]
        (Localization.AtPrime Q ⧸ (P i).map (algebraMap R (Localization.AtPrime Q)))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
      ∑ i ∈ Finset.range n, if P i = Q then 1 else 0 := by
  rw [module_length_eq_sum_filtration N hmono hzero n htop]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(e i (Finset.mem_range.mp hi)).length_eq]
  exact localized_prime_factor_length I (P i) Q hQ (hIP i (Finset.mem_range.mp hi))

end PiExponentJets.W22

end OAI
