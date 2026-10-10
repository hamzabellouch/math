import Mathlib
import OAI.Computability.QuantumFactoring.FlatVerifiedData

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

lemma divisorPrimes_subset (m : ℕ) (ps : List ℕ) : divisorPrimes m ps ⊆ ps := by
  induction ps generalizing m with
  | nil=>simp [divisorPrimes]
  | cons p ps ih=>
    intro q hq
    rw [divisorPrimes] at hq
    split_ifs at hq
    · rcases List.mem_cons.mp hq with rfl|hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hq)
    · exact List.mem_cons_of_mem _ (ih _ hq)

lemma primeRecord_support_subset (ps : List ℕ) : ∀ p∈(primeRecord ps).support,p∈ps := by
  induction ps with
  | nil=>simp [primeRecord]
  | cons q qs ih=>
    intro p hp
    have hp':=(Finsupp.mem_support_iff).mp hp
    by_cases he : p=q
    · subst p; exact List.mem_cons_self
    · have htail : (primeRecord qs) p≠0 := by
        simpa only [primeRecord,Finsupp.add_apply,Finsupp.single_eq_of_ne he,zero_add] using hp'
      exact List.mem_cons_of_mem _ (ih p (Finsupp.mem_support_iff.mpr htail))

namespace PhysicalTree
/-- A fixed rectangular table of prime candidates. Unused rows and zero
padding become 2. This requires no support enumeration or factor search. -/
def tableFactors (rows : List (ℕ×List ℕ)) : List ℕ :=
  rows.flatMap (fun r=>r.2.map (fun p=>if r.1=0 ∨ p=0 then 2 else p))

lemma tableFactors_prime {n N : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) : ∀ p∈tableFactors rows,p.Prime := by
  intro p hp
  obtain ⟨r,hr,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  split_ifs with hz
  · exact Nat.prime_two
  · have hr0 : r.1≠0 := fun he=>hz (Or.inl he)
    have hq0 : q≠0 := fun he=>hz (Or.inr he)
    have hv:=(h.2.1 r hr).resolve_left hr0
    exact (encoding_filter hv).1 q (List.mem_filter.mpr ⟨hq,by simpa using hq0⟩)

lemma lookupPrimes_subset_table {rows : List (ℕ×List ℕ)} {M : ℕ} (hM : M≠0) :
    lookupPrimes rows M ⊆ tableFactors rows := by
  intro p hp
  obtain ⟨hp,hp0⟩:=List.mem_filter.mp hp
  have hp0 : p≠0 := by simpa only [decide_eq_true_eq] using hp0
  cases hf : rows.find? (fun r=>decide (r.1=M)) with
  | none=>simp only [lookupFields,hf,List.not_mem_nil] at hp
  | some r=>
    have hr:=List.mem_of_find?_eq_some hf
    have he : r.1=M := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hpr : p∈r.2 := by simpa only [lookupFields,hf] using hp
    apply List.mem_flatMap.mpr
    refine ⟨r,hr,List.mem_map.mpr ⟨p,hpr,?_⟩⟩
    rw [ite_eq_right (by simp only [he,hM,hp0,or_self,not_false_eq_true])]

lemma logTotientPrimes_subset_table {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0) (_hd : m∣M) :
    logTotientPrimes rows M m ⊆ tableFactors rows := by
  intro p hp
  obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
  have hq' := primeRecord_support_subset (logDivisorPrimes rows M m) q
    ((Finset.mem_sort (·≤·)).mp hq)
  have hqparent : q∈lookupPrimes rows M := divisorPrimes_subset m _ hq'
  have hqprime := (lookupPrimes_correct h hM hM0).1 q hqparent
  rcases List.mem_append.mp hp with hp|hp
  · have he:=(List.mem_replicate.mp hp).2
    subst p
    exact lookupPrimes_subset_table hM0 hqparent
  · split_ifs at hp with h2
    · simp at hp
    · exact lookupPrimes_subset_table (by have:=hqprime.two_le; omega) hp

/-- A support-covering list gives a known multiple after n repetitions,
because every prime exponent of an n-bit positive integer is at most n. -/
lemma dvd_cover_power {v n : ℕ} (ps : List ℕ) (hv : v≠0) (hb : v≤2^n)
    (hp : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p∣v→p∈ps) : v∣ps.prod^n := by
  have hprod : ps.prod≠0 := List.prod_ne_zero (by intro h;exact (hp 0 h).ne_zero rfl)
  apply (Nat.factorization_prime_le_iff_dvd hv (pow_ne_zero _ hprod)).mp
  intro p hprime
  by_cases hd : p∣v
  · have hm:=hcover p hprime hd
    have hpd : p∣ps.prod := List.dvd_prod hm
    have hpos : 1≤ps.prod.factorization p := (hprime.factorization_pos_of_dvd hprod hpd)
    have he : v.factorization p≤n := Nat.factorization_le_of_le_pow
      (hb.trans (Nat.pow_le_pow_left hprime.two_le n))
    rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    exact he.trans (by nlinarith)
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- A rectangular verified data table is sufficient to recover the same
literal multiplicative order. No unbounded support extraction is required. -/
theorem table_strip_order {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m<2^n) (hd : m∣M) (a : (ZMod m)ˣ) :
    stripOrderFactors a (List.flatten (List.replicate n (tableFactors rows)))
      ((tableFactors rows).prod^n)=orderOf a := by
  let : NeZero m := ⟨by omega⟩
  have hc:=logTotientPrimes_correct h hM hM0 (by omega : 0 < m) hd
  have hcover : ∀ p : ℕ,p.Prime→p∣m.totient→p∈tableFactors rows := by
    intro p hp hpd
    have mem : p∈logTotientPrimes rows M m := by
      have hpd' : p∣(logTotientPrimes rows M m).prod := by rwa [hc.2]
      obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpd'
      have he:=((hc.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
      simpa only [he] using hq
    exact logTotientPrimes_subset_table h hM hM0 hd mem
  have hphi : m.totient∣(tableFactors rows).prod^n := dvd_cover_power _
    (Nat.totient_pos.mpr (by omega : 0 < m)).ne'
    ((Nat.totient_le m).trans hb.le) (tableFactors_prime h) hcover
  have horder : orderOf a∣m.totient := by
    simpa [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using orderOf_dvd_natCard a
  have hmul := Nat.mul_div_cancel' (horder.trans hphi)
  rw [←hmul]
  apply stripOrderFactors_exact a (orderOf_pos a)
  · intro p hp
    obtain ⟨xs,hxs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hxs).2
    subst xs
    exact tableFactors_prime h p hp
  · have he : (List.flatten (List.replicate n (tableFactors rows))).prod=
        (tableFactors rows).prod^n := by
      rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
    rw [he]
    exact Nat.div_dvd_of_dvd (horder.trans hphi)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
