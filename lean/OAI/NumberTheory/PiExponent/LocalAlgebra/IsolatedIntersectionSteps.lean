import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination

namespace OAI

namespace PiExponentSiegel.W17.IsolatedIntersection

variable {R : Type*} [CommRing R]

theorem minimalPrime_over_parent_intersection {I P Q : Ideal R} {f : R}
    (hQ : Q ∈ (I ⊔ Ideal.span {f}).minimalPrimes)
    (hIP : I ≤ P) (hPQ : P ≤ Q) :
    Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
  refine ⟨⟨hQ.1.1, sup_le hPQ (le_sup_right.trans hQ.1.2)⟩, ?_⟩
  intro S hS hSQ
  exact hQ.2 ⟨hS.1, sup_le (hIP.trans (le_sup_left.trans hS.2))
    (le_sup_right.trans hS.2)⟩ hSQ

theorem exists_minimalPrime_parent {I Q : Ideal R} {f : R}
    (hQ : Q ∈ (I ⊔ Ideal.span {f}).minimalPrimes) :
    ∃ P ∈ I.minimalPrimes, P ≤ Q ∧
      Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
  let : Q.IsPrime := hQ.1.1
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.1.2)
  exact ⟨P, hP, hPQ, minimalPrime_over_parent_intersection hQ hP.1.2 hPQ⟩

theorem local_regular_avoids_retained_minimalPrime
    (I T : Ideal R) [T.IsPrime] {Q : Ideal R} {f : R}
    (hQ : Q ∈ I.minimalPrimes) (hQT : Q ≤ T)
    (hreg : IsSMulRegular
      (Localization.AtPrime T ⧸ I.map (algebraMap R (Localization.AtPrime T)))
      (algebraMap R (Localization.AtPrime T) f)) : f ∉ Q := by
  let L := Localization.AtPrime T
  let a : R →+* L := algebraMap R L
  have hd : Disjoint (T.primeCompl : Set R) (Q : Set R) := by
    apply Set.disjoint_left.mpr
    intro x hx hxQ
    exact (show x ∉ T from hx) (hQT hxQ)
  have hc : (Q.map a).comap a = Q :=
    IsLocalization.under_map_of_isPrime_disjoint T.primeCompl L hQ.1.1 hd
  have hm : Q.map a ∈ (I.map a).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map T.primeCompl L]
    change (Q.map a).comap a ∈ I.minimalPrimes
    rw [hc]
    exact hQ
  have hnot : a f ∉ Q.map a := hreg.notMem_of_mem_minimalPrimes
    (by simpa only [Ideal.annihilator_quotient] using hm)
  exact fun hf => hnot (Ideal.mem_map_of_mem a hf)

theorem exists_component_chain (J : ℕ → Ideal R)
    (hstep : ∀ i, J i ≤ J (i + 1)) (n : ℕ) (T : Ideal R)
    (hT : T ∈ (J n).minimalPrimes) :
    ∃ C : ℕ → Ideal R, C n = T ∧
      (∀ i ≤ n, C i ∈ (J i).minimalPrimes ∧ C i ≤ T) ∧
      (∀ i < n, C i ≤ C (i + 1)) := by
  classical
  induction n generalizing T with
  | zero =>
    refine ⟨fun _ => T, rfl, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      exact ⟨hT, le_rfl⟩
    · intro i hi
      omega
  | succ n ih =>
    let : T.IsPrime := hT.1.1
    obtain ⟨P, hP, hPT⟩ := Ideal.exists_minimalPrimes_le ((hstep n).trans hT.1.2)
    obtain ⟨C, hCn, hC, hmono⟩ := ih P hP
    let D : ℕ → Ideal R := fun i => if i ≤ n then C i else T
    refine ⟨D, by simp [D], ?_, ?_⟩
    · intro i hi
      by_cases hin : i ≤ n
      · have hx : C i ∈ (J i).minimalPrimes ∧ C i ≤ T :=
          ⟨(hC i hin).1, (hC i hin).2.trans hPT⟩
        simpa [D, hin] using hx
      · have heq : i = n + 1 := by omega
        subst i
        have hx : T ∈ (J (n + 1)).minimalPrimes ∧ T ≤ T := ⟨hT, le_rfl⟩
        simpa [D] using hx
    · intro i hi
      by_cases hin : i < n
      · have hi₁ : i ≤ n := by omega
        have hi₂ : i + 1 ≤ n := by omega
        simpa [D, hi₁, hi₂] using hmono i hin
      · have heq : i = n := by omega
        subst i
        simpa [D, hCn] using hPT

theorem exists_proper_component_chain
    (J : ℕ → Ideal R) (f : ℕ → R)
    (hstep : ∀ i, J (i + 1) = J i ⊔ Ideal.span {f i})
    (n : ℕ) (T : Ideal R) [T.IsPrime]
    (hT : T ∈ (J n).minimalPrimes)
    (hreg : ∀ i < n, IsSMulRegular
      (Localization.AtPrime T ⧸ (J i).map (algebraMap R (Localization.AtPrime T)))
      (algebraMap R (Localization.AtPrime T) (f i))) :
    ∃ C : ℕ → Ideal R, C n = T ∧
      (∀ i ≤ n, C i ∈ (J i).minimalPrimes ∧ C i ≤ T) ∧
      (∀ i < n, f i ∉ C i ∧ C i < C (i + 1) ∧
        C (i + 1) ∈ (C i ⊔ Ideal.span {f i}).minimalPrimes) := by
  have hmono : ∀ i, J i ≤ J (i + 1) := by
    intro i
    rw [hstep]
    exact le_sup_left
  obtain ⟨C, hCn, hC, hCC⟩ := exists_component_chain J hmono n T hT
  refine ⟨C, hCn, hC, ?_⟩
  intro i hi
  have hi₁ : i ≤ n := Nat.le_of_lt hi
  have hi₂ : i + 1 ≤ n := hi
  have hnot := local_regular_avoids_retained_minimalPrime (J i) T
    (hC i hi₁).1 (hC i hi₁).2 (hreg i hi)
  have hnext : C (i + 1) ∈ (J i ⊔ Ideal.span {f i}).minimalPrimes := by
    rw [← hstep]
    exact (hC (i + 1) hi₂).1
  have hmin := minimalPrime_over_parent_intersection hnext (hC i hi₁).1.1.2 (hCC i hi)
  refine ⟨hnot, lt_of_le_of_ne (hCC i hi) ?_, hmin⟩
  intro heq
  apply hnot
  rw [heq]
  exact hnext.1.2 ((show Ideal.span {f i} ≤ J i ⊔ Ideal.span {f i} from
    le_sup_right) (Ideal.subset_span (Set.mem_singleton _)))

theorem completeIdeal_not_le_proper_parent {J T P : Ideal R}
    (hT : T ∈ J.minimalPrimes) (hP : P.IsPrime) (hPT : P < T) : ¬ J ≤ P := by
  intro hJP
  exact (not_le_of_gt hPT) (hT.2 ⟨hP, hJP⟩ hPT.le)

variable {K ι τ : Type*} [Field K] [Infinite K] [Algebra K R] [Finite ι]

theorem exists_generatorCombination_avoiding_parents
    (g : τ → R) (T : Ideal R)
    (hT : T ∈ (Ideal.span (Set.range g)).minimalPrimes)
    (P : ι → Ideal R) (hP : ∀ i, (P i).IsPrime) (hPT : ∀ i, P i < T) :
    ∃ c : τ →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply PiExponentSiegel.W20.exists_linearCombination_avoiding_ideals g P
  exact fun i => completeIdeal_not_le_proper_parent hT (hP i) (hPT i)

end PiExponentSiegel.W17.IsolatedIntersection

end OAI
