import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.SimpleModule.Basic
import OAI.NumberTheory.SiegelZeros.Structure.CyclicPrimeFactor

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem length_filtration_step (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R B = Module.length R A + Module.length R (B ⧸ A.submoduleOf B) := by
  have h := Module.length_eq_add_of_exact (A.submoduleOf B).subtype
    (A.submoduleOf B).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(Submodule.submoduleOfEquivOfLe hAB).length_eq] at h
  exact h

theorem length_eq_sum_filtration
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (hzero : N 0 = ⊥) (n : ℕ) :
    Module.length R (N n) =
      ∑ i ∈ Finset.range n, Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have hlen := congrArg (fun A : Submodule R M => Module.length R A) hzero
    exact hlen.trans Module.length_eq_zero
  | succ n ih =>
    rw [length_filtration_step (N n) (N (n + 1)) (hmono n), ih,
      Finset.sum_range_succ]

theorem module_length_eq_sum_filtration
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (hzero : N 0 = ⊥) (n : ℕ) (htop : N n = ⊤) :
    Module.length R M =
      ∑ i ∈ Finset.range n, Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  have hlen := congrArg (fun A : Submodule R M => Module.length R A) htop
  have hlen' : Module.length R (N n) = Module.length R M :=
    hlen.trans Module.length_top
  exact hlen'.symm.trans (length_eq_sum_filtration N hmono hzero n)

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def subquotientEquivImage (A B : Submodule R M) :
    (B ⧸ A.submoduleOf B) ≃ₗ[R] B.map A.mkQ := by
  let F : B →ₗ[R] M ⧸ A := A.mkQ.comp B.subtype
  have hker : LinearMap.ker F = A.submoduleOf B := by
    simp only [F, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.submoduleOf]
  have hrange : LinearMap.range F = B.map A.mkQ := by
    simp only [F, LinearMap.range_comp, Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

theorem quotient_length_step (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R (M ⧸ A) =
      Module.length R (B ⧸ A.submoduleOf B) + Module.length R (M ⧸ B) := by
  let T : Submodule R (M ⧸ A) := B.map A.mkQ
  have h := Module.length_eq_add_of_exact T.subtype T.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  change Module.length R (M ⧸ A) = Module.length R (B.map A.mkQ) +
    Module.length R ((M ⧸ A) ⧸ B.map A.mkQ) at h
  rw [← (subquotientEquivImage A B).length_eq,
    (Submodule.quotientQuotientEquivQuotient A B hAB).length_eq] at h
  exact h

theorem quotient_length_eq_sum_and_last
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1)) (n : ℕ) :
    Module.length R (M ⧸ N 0) =
      (∑ i ∈ Finset.range n,
        Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1)))) +
      Module.length R (M ⧸ N n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, quotient_length_step (N n) (N (n + 1)) (hmono n),
      Finset.sum_range_succ, add_assoc]

theorem quotient_length_eq_sum_of_last_top
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (n : ℕ) (htop : N n = ⊤) :
    Module.length R (M ⧸ N 0) =
      ∑ i ∈ Finset.range n,
        Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  have heq := congrArg (fun A : Submodule R M => Module.length R (M ⧸ A)) htop
  have hz : Module.length R (M ⧸ N n) = 0 := heq.trans Module.length_eq_zero
  simpa only [hz, add_zero] using quotient_length_eq_sum_and_last N hmono n

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

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

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

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
    simp only
    exact localized_prime_factor_length_one Q
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

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

theorem localized_cyclic_filtration_length
    (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
    (J : ℕ → Ideal R) (hmono : ∀ i, J i ≤ J (i + 1))
    (hstart : J 0 = I) (n : ℕ) (hend : J n = ⊤)
    (f : ℕ → R)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hprime : ∀ i < n, ((J i).colon {f i}).IsPrime) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
      ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  let L := Localization.AtPrime Q
  let N : ℕ → Ideal L := fun i => (J i).map (algebraMap R L)
  have hNmono : ∀ i, N i ≤ N (i + 1) := fun i => Ideal.map_mono (hmono i)
  have hNtop : N n = ⊤ := by simp only [N, hend, Ideal.map_top]
  have hstartlen := congrArg
    (fun A : Ideal R => Module.length L (L ⧸ A.map (algebraMap R L))) hstart
  have hlen := quotient_length_eq_sum_of_last_top N hNmono n hNtop
  have hbase : I ≤ J 0 := hstart.symm.le
  have hIle : ∀ i, I ≤ J i := fun i =>
    hbase.trans ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  calc
    _ = Module.length L (L ⧸ N 0) := hstartlen.symm
    _ = ∑ i ∈ Finset.range n,
        Module.length L (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := hlen
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      let := hprime i hin
      have hIP : I ≤ (J i).colon {f i} := by
        intro a ha
        apply Submodule.mem_colon_singleton.mpr
        exact (J i).mul_mem_right (f i) (hIle i ha)
      have heq : Module.length L (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) =
          Module.length L (L ⧸ ((J i).colon {f i}).map (algebraMap R L)) := by
        have htransport := congrArg
          (fun K : Ideal R => Module.length L
            (↥(K.map (algebraMap R L)) ⧸
              ((J i).map (algebraMap R L)).submoduleOf (K.map (algebraMap R L))))
          (hstep i hin)
        exact htransport.trans
          (primeLocalizedCyclicFactorEquiv Q (J i) (f i)).symm.length_eq
      rw [heq]
      exact localized_prime_factor_length I ((J i).colon {f i}) Q hQ hIP

end WeightedTorusJets.W22


end SiegelZeros

end OAI
