import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveOrder
import OAI.Computability.QuantumFactoring.PrimeRecords

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- Expand ONLY the supplied exponent record. No factoring operation is hidden
in the list used by the retrospective controller. -/
def recordPrimes (f : FactorRecord) : List ℕ :=
  (f.support.sort (· ≤ ·)).flatMap (fun p => List.replicate (f p) p)

lemma recordPrimes_prime {f : FactorRecord} (hp : ∀ p∈f.support,p.Prime) :
    ∀ p∈recordPrimes f,p.Prime := by
  intro p h
  obtain ⟨q,hq,hp'⟩ := List.mem_flatMap.mp h
  have he : p=q := (List.mem_replicate.mp hp').2
  subst p
  exact hp q ((Finset.mem_sort (· ≤ ·)).mp hq)

lemma recordPrimes_prod (f : FactorRecord) : (recordPrimes f).prod=f.prod (·^·) := by
  rw [recordPrimes,prod_flatMap]
  simp only [List.prod_replicate]
  rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  rfl

lemma recordPrimes_length (f : FactorRecord) : (recordPrimes f).length=f.sum (fun _ e => e) := by
  rw [recordPrimes,List.length_flatMap]
  simp only [List.length_replicate]
  rw [←List.sum_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  rfl

/-- Divide a subfactor from the parent's prime list, in bounded time: there is
at most one division per prime occurrence in the already supplied list. -/
def divisorPrimes : ℕ→List ℕ→List ℕ
  | _, [] => []
  | m, p::ps => if p∣m then p::divisorPrimes (m/p) ps else divisorPrimes m ps

lemma divisorPrimes_length (m : ℕ) (ps : List ℕ) : (divisorPrimes m ps).length ≤ ps.length := by
  induction ps generalizing m with
  | nil => simp [divisorPrimes]
  | cons p ps ih =>
    rw [divisorPrimes]
    split_ifs
    · exact Nat.succ_le_succ (ih _)
    · exact (ih _).trans (by simp)

lemma divisorPrimes_prime (m : ℕ) (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) :
    ∀ p∈divisorPrimes m ps,p.Prime := by
  induction ps generalizing m with
  | nil => simp [divisorPrimes]
  | cons p ps ih =>
    have htail : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    rw [divisorPrimes]
    split_ifs
    · intro q hq
      rcases List.mem_cons.mp hq with he | hq
      · subst q; exact hp p (by simp)
      · exact ih _ htail q hq
    · exact ih _ htail

lemma divisorPrimes_prod (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) {m : ℕ} (hd : m∣ps.prod) :
    (divisorPrimes m ps).prod=m := by
  induction ps generalizing m with
  | nil =>
    have hm := Nat.dvd_one.mp hd
    simp [divisorPrimes,hm]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have htail : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    rw [divisorPrimes]
    split_ifs with hdiv
    · rw [List.prod_cons,ih htail (quotient_dvd_tail hprime.pos hdiv hd),Nat.mul_div_cancel' hdiv]
    · exact ih htail ((hprime.coprime_iff_not_dvd.mpr hdiv).symm.dvd_of_dvd_mul_left hd)

/-- Literal stored record projection, used only after complete-data validation. -/
def FactorData.factors : FactorData→FactorRecord
  | .node _ f _ => f

def FactorData.descendants : FactorData→List FactorData
  | .node _ _ ds => ds

@[simp] lemma trueData_factors (m : ℕ) : (trueData m).factors=m.factorization := by
  rw [trueData_eq]; rfl
@[simp] lemma trueData_descendants (m : ℕ) : (trueData m).descendants=(children m).map trueData := by
  rw [trueData_eq]; rfl

def dataDivisorPrimes (data : FactorData) (m : ℕ) : List ℕ :=
  divisorPrimes m (recordPrimes data.factors)

lemma dataDivisorPrimes_correct {M m : ℕ} (hM : 0<M) (hd : m∣M) :
    (∀ p∈dataDivisorPrimes (trueData M) m,p.Prime) ∧
      (dataDivisorPrimes (trueData M) m).prod=m := by
  have hp : ∀ p∈recordPrimes M.factorization,p.Prime :=
    recordPrimes_prime (fun _ => Nat.prime_of_mem_primeFactors)
  have hprod : (recordPrimes M.factorization).prod=M := by
    rw [recordPrimes_prod,Nat.prod_factorization_pow_eq_self hM.ne']
  refine ⟨?_,?_⟩
  · simpa only [dataDivisorPrimes,trueData_factors] using divisorPrimes_prime m _ hp
  · simpa only [dataDivisorPrimes,trueData_factors] using divisorPrimes_prod _ hp (show m∣(recordPrimes M.factorization).prod by rw [hprod]; exact hd)

/-- Child lookup takes the first matching stored occurrence. It does not compute
new children. Distinct parents deliberately retain separate occurrence data. -/
def dataChildPrimes (data : FactorData) (label : ℕ) : List ℕ :=
  match data.descendants.find? (fun d => decide (d.label=label)) with
  | none => []
  | some d => recordPrimes d.factors

lemma dataChildPrimes_correct {M label : ℕ} (h : label∈children M) :
    (∀ p∈dataChildPrimes (trueData M) label,p.Prime) ∧
      (dataChildPrimes (trueData M) label).prod=label := by
  have hex : ∃ d, ((children M).map trueData).find? (fun d => decide (d.label=label))=some d := by
    cases hf : ((children M).map trueData).find? (fun d => decide (d.label=label)) with
    | none =>
      have hh := List.find?_eq_none.mp hf (trueData label) (List.mem_map.mpr ⟨label,h,rfl⟩)
      simp only [trueData_label,decide_true] at hh
      contradiction
    | some d => exact ⟨d,rfl⟩
  obtain ⟨d,hd⟩ := hex
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hd)
  have he : l=label := by simpa only [trueData_label,decide_eq_true_eq] using List.find?_some hd
  subst l
  have hlabel := (child_bounds h).1
  simp only [dataChildPrimes,trueData_descendants,hd,trueData_factors]
  refine ⟨recordPrimes_prime (fun _ => Nat.prime_of_mem_primeFactors),?_⟩
  rw [recordPrimes_prod,Nat.prod_factorization_pow_eq_self (by omega)]

/-- phi factors are reconstructed from division against the supplied parent
record and the supplied p−1 children. The p=2 contribution requires no child. -/
noncomputable def dataTotientPrimes (data : FactorData) (m : ℕ) : List ℕ :=
  let f := primeRecord (dataDivisorPrimes data m)
  (f.support.sort (· ≤ ·)).flatMap (fun p =>
    List.replicate (f p-1) p ++ if p=2 then [] else dataChildPrimes data (p-1))

lemma dataTotientPrimes_correct {M m : ℕ} (hM : 0<M) (hm : 0 < m) (hd : m∣M) :
    (∀ p∈dataTotientPrimes (trueData M) m,p.Prime) ∧
      (dataTotientPrimes (trueData M) m).prod=m.totient := by
  obtain ⟨hprime,hprod⟩ := dataDivisorPrimes_correct hM hd
  have hf : primeRecord (dataDivisorPrimes (trueData M) m)=m.factorization := by
    rw [primeRecord_eq_factorization _ hprime,hprod]
  have hchild (p : ℕ) (hp : p∈m.factorization.support) (h2 : p≠2) :
      p-1∈children M := by
    have hpm : p.Prime ∧ p∣m ∧ m≠0 := Nat.mem_primeFactors.mp hp
    exact mem_children.mpr ⟨p,hpm.1,hpm.2.1.trans hd,hM.ne',by have := hpm.1.two_le; omega,rfl⟩
  rw [dataTotientPrimes,hf]
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
    have hq' := (Finset.mem_sort (· ≤ ·)).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · have he := (List.mem_replicate.mp hp).2
      subst p
      exact Nat.prime_of_mem_primeFactors hq'
    · split_ifs at hp with h2
      · simp at hp
      · exact (dataChildPrimes_correct (hchild q hq' h2)).1 p hp
  · rw [prod_flatMap]
    calc
      _ = ((m.factorization.support.sort (· ≤ ·)).map
          (fun p => p^(m.factorization p-1)*(p-1))).prod := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [List.prod_append,List.prod_replicate]
        split_ifs with h2
        · subst p
          simp
        · rw [(dataChildPrimes_correct (hchild p ((Finset.mem_sort (· ≤ ·)).mp hp) h2)).2]
      _ = m.factorization.prod (fun p e => p^(e-1)*(p-1)) := by
        rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
        rfl
      _ = m.totient := (Nat.totient_eq_prod_factorization hm.ne').symm

/-- Section5's retrospective order algorithm instantiated with the **actual
supplied auxiliary data**, not with a hypothesized factorization of phi. -/
theorem data_strip_order {M m : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M)
    (a : (ZMod m)ˣ) :
    stripOrderFactors a (dataTotientPrimes (trueData M) m) m.totient=orderOf a := by
  obtain ⟨hp,hprod⟩ := dataTotientPrimes_correct hM (by omega) hd
  exact strip_totient_factors hm a _ hp hprod

end ExactQuantumFactoring


end

end OAI
