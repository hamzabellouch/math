import OAI.NumberTheory.Jacobsthal.Estimates.HypotheticalSubbinLower
import OAI.NumberTheory.Jacobsthal.Sieve.LastPrimeModulusCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  ErdosInverseCounts ErdosInverseAlignment ErdosHypotheticalTag
  ErdosPrimeInputs.MertensStrong NumberTheoryLean

attribute [local instance] Classical.propDecidable

noncomputable def primeHypothetical (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q p : ℕ) : ℝ :=
  if hp : p.Prime then
    (modulusCount Y small (@hypotheticalClass a r p ⟨hp.ne_zero⟩) (p*q) : ℝ)
  else 0

theorem primeHypothetical_on_prime (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q p : ℕ) (hp : p.Prime) :
    primeHypothetical Y small a r q p =
      (modulusCount Y small (@hypotheticalClass a r p ⟨hp.ne_zero⟩) (p*q) : ℝ) := by
  simp only [primeHypothetical,dite_eq_left hp]

theorem primeHypothetical_row (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) (p : T) :
    primeHypothetical Y small a r q p.val=hypotheticalRowCount Y small T a r q hT p := by
  exact primeHypothetical_on_prime Y small a r q p.val (hT p.val p.property)

theorem primeHypothetical_sum (Y : ℕ) (small T : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q : ℕ) (hT : ∀ p ∈ T,p.Prime) :
    (∑ p ∈ T,primeHypothetical Y small a r q p)=
      ∑ p : T,hypotheticalRowCount Y small T a r q hT p := by
  rw [← Finset.sum_coe_sort T]
  exact Finset.sum_congr rfl (fun p _ => primeHypothetical_row Y small T a r q hT p)

theorem primeHypothetical_agrees (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (q p : ℕ) (hp : p.Prime) (ha : aligns (fun t => (a t : ℤ)) r p) :
    primeHypothetical Y small a r q p=(modulusCount Y small a (p*q) : ℝ) := by
  rw [primeHypothetical_on_prime Y small a r q p hp]
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [hypothetical_count_agrees Y small a r (p*q) p hp ha]

theorem strict_smallPrimeSet_nat (P : ℕ) :
    smallPrimeSet (P : ℝ)=LargePrimeDeletion.cutoffPrimes (P-1) := by
  ext t
  rw [mem_smallPrimeSet,LargePrimeDeletion.mem_cutoffPrimes]
  constructor
  · rintro ⟨ht,hlt⟩
    have hlt' : t < P := by exact_mod_cast hlt
    exact ⟨ht,by omega⟩
  · rintro ⟨ht,hle⟩
    have hlt : t < P := by have := ht.two_le;omega
    exact ⟨ht,by exact_mod_cast hlt⟩

theorem primeHypothetical_uniform_upper :
    ∃ C eta0 : ℝ,0 < C ∧ 0 < eta0 ∧ eta0 ≤ 1/4 ∧ 2*C*eta0 ≤ 1/20 ∧
      ∃ P0 : ℕ,2 ≤ P0 ∧ ∀ P : ℕ,P.Prime → P0 ≤ P →
        ∀ Y q p : ℕ,∀ r : ℚ,∀ a : ℕ → ℕ,
        0 < Y → p.Prime → Squarefree (p*q) →
        (∀ t ∈ (p*q).primeFactors,P ≤ t) → (P : ℝ)^2 ≤ (Y : ℝ)/(p*q : ℕ) →
        primeHypothetical Y (smallPrimeSet (P : ℝ)) a r q p ≤
          C*((Y : ℝ)/(p*q : ℕ))*primeProduct (P : ℝ) := by
  obtain ⟨C,hC,P0,hP0,hUpper⟩ := original_individual_upper_closed
  refine ⟨C,min (1/4) (1/(40*C)),hC,lt_min (by norm_num) (by positivity),
    min_le_left _ _,?_,P0,hP0,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (min_le_right (1/4 : ℝ) (1/(40*C)))
      (show 0 ≤ 2*C by positivity)
    have he : 2*C*(1/(40*C))=(1/20 : ℝ) := by field_simp;ring
    exact hh.trans_eq he
  · intro P hPrime hP Y q p r a hY hp hsf hlarge hJ
    rw [primeHypothetical_on_prime Y _ a r q p hp,strict_smallPrimeSet_nat]
    exact hUpper P hPrime hP Y (p*q) _ hY hsf hlarge hJ

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open ErdosInverseCounts ErdosInverseAlignment ErdosStoppedTagSieve
  NumberTheoryLean.LastPrimeModulusCount


theorem prime_word_product (ps : List ℕ) (hd : ps.Pairwise (· > ·))
    (hprime : ∀ p ∈ ps,p.Prime) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ps.prod.primeFactors=ps.toFinset := by
  have hn : ps.Nodup := hd.imp (fun h => ne_of_gt h)
  have hpos : 0 < ps.prod := List.prod_pos (fun p hp => (hprime p hp).pos)
  have he : (∏ p ∈ ps.toFinset,p)=ps.prod := by
    simpa only [List.map_id'] using List.prod_toFinset (fun p : ℕ => p) hn
  have hprimeF : ∀ p ∈ ps.toFinset,p.Prime := fun p hp => hprime p (List.mem_toFinset.mp hp)
  have hsq : Squarefree (∏ p ∈ ps.toFinset,p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      simp only [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprimeF p hp) (hprimeF q hq)).mpr hpq
    · exact fun p hp => (hprimeF p hp).squarefree
  refine ⟨hpos,by rwa [he] at hsq,?_⟩
  rw [← he]
  exact primeFactors_product ps.toFinset hprimeF

theorem last_prime_mem (ps : List ℕ) (hne : ps≠[]) : ps.getLastD 0 ∈ ps := by
  rw [← List.dropLast_append_getLast hne,List.getLastD_concat]
  simp

theorem fixed_tail_arithmetic (pre tail : List ℕ) (p : ℕ) (htail : tail ≠ [])
    (hd : (pre++p::tail).Pairwise (· > ·))
    (hprime : ∀ t ∈ pre++p::tail,t.Prime) (a : ℕ → ℤ) (r : ℚ)
    (hAlign : ∀ t ∈ pre++tail,aligns a r t) :
    (tail.getLastD 0).Prime ∧ 0 < pre.prod*tail.prod ∧
      Squarefree (p*(pre.prod*tail.prod)) ∧
      (∀ t ∈ (p*(pre.prod*tail.prod)).primeFactors,tail.getLastD 0 ≤ t) ∧
      p ∉ smallPrimeSet (tail.getLastD 0 : ℝ) ∧
      (∀ t ∈ smallPrimeSet (tail.getLastD 0 : ℝ),(pre.prod*tail.prod).Coprime t) ∧
      ∀ t ∈ (p*(pre.prod*tail.prod)).primeFactors,t ≠ p → aligns a r t := by
  have hLastTail := last_prime_mem tail htail
  have hLast : (tail.getLastD 0).Prime := hprime _
    (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hLastTail))))
  have hprod := prime_word_product (pre++p::tail) hd hprime
  have he : (pre++p::tail).prod=p*(pre.prod*tail.prod) := by
    simp only [List.prod_append,List.prod_cons];ring
  rw [he] at hprod
  have hqpos : 0 < pre.prod*tail.prod := by
    by_contra hn
    have hz : pre.prod*tail.prod=0 := by omega
    have hh := hprod.1
    rw [hz,mul_zero] at hh
    omega
  have hlastWord : (pre++p::tail).getLastD 0=tail.getLastD 0 := by
    rw [← List.dropLast_append_getLast htail]
    rw [← List.cons_append,← List.append_assoc]
    simp only [List.getLastD_concat]
  have hlow : ∀ t ∈ (p*(pre.prod*tail.prod)).primeFactors,tail.getLastD 0 ≤ t := by
    have hh := (below_all_last (pre++p::tail) (by simp) hd (tail.getLastD 0-1)).mpr
      (by rw [hlastWord];exact Nat.sub_lt hLast.pos (by norm_num))
    intro t ht
    rw [hprod.2.2] at ht
    have h := hh t (List.mem_toFinset.mp ht)
    omega
  have hPp : tail.getLastD 0 < p :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hd).2.1).1 _ hLastTail
  refine ⟨hLast,hqpos,hprod.2.1,hlow,?_,?_,?_⟩
  · intro hp
    have hh := ((mem_smallPrimeSet _ p).mp hp).2
    have hpp : (tail.getLastD 0 : ℝ) < p := by exact_mod_cast hPp
    linarith
  · intro t ht
    obtain ⟨htPrime,htP⟩ := (mem_smallPrimeSet _ t).mp ht
    apply Nat.Coprime.symm
    apply htPrime.coprime_iff_not_dvd.mpr
    intro htq
    have htd : t ∣ p*(pre.prod*tail.prod) := dvd_mul_of_dvd_right htq p
    have htf : t ∈ (p*(pre.prod*tail.prod)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨htPrime,htd,hprod.1.ne'⟩
    have h := hlow t htf
    have htP' : t < tail.getLastD 0 := by exact_mod_cast htP
    omega
  · intro t ht hne
    rw [hprod.2.2] at ht
    have hm := List.mem_toFinset.mp ht
    apply hAlign t
    simp only [List.mem_append,List.mem_cons] at hm ⊢
    tauto

end ErdosStoppedArithmetic


end Erdos970

end OAI
