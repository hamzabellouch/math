import Mathlib
import OAI.Computability.QuantumFactoring.TableOrder

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Strip a given prime multiset, updating Euler's totient one prime factor
at a time. The supplied list may contain redundant factors. -/
def totientScan : List ℕ → ℕ → ℕ
  | [], _ => 1
  | p::ps, v => if p ∣ v then
      (if p ∣ v/p then p else p-1)*totientScan ps (v/p)
    else totientScan ps v

lemma totientScan_exact (ps : List ℕ) (v : ℕ) (hv : 0 < v)
    (hp : ∀ p∈ps,p.Prime) (hd : v ∣ ps.prod) : totientScan ps v=v.totient := by
  induction ps generalizing v with
  | nil=>
    have he : v=1 := Nat.eq_one_of_dvd_one hd
    subst v
    simp [totientScan]
  | cons p ps ih=>
    have hprime:=hp p (List.mem_cons_self)
    have hps : ∀ q∈ps,q.Prime := fun q hq=>hp q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons] at hd
    rw [totientScan]
    by_cases hdv : p ∣ v
    · rw [ite_eq_left hdv]
      have he : p*(v/p)=v := Nat.mul_div_cancel' hdv
      have hd' : v/p ∣ ps.prod := by
        apply (Nat.mul_dvd_mul_iff_left hprime.pos).mp
        rwa [he]
      have hv' : 0 < v/p := by
        exact Nat.div_pos (Nat.le_of_dvd hv hdv) hprime.pos
      rw [ih (v/p) hv' hps hd']
      conv_rhs => rw [←he]
      by_cases hpp : p ∣ v/p
      · rw [ite_eq_left hpp,Nat.totient_mul_of_prime_of_dvd hprime hpp]
      · rw [ite_eq_right hpp,Nat.totient_mul_of_prime_of_not_dvd hprime hpp]
    · rw [ite_eq_right hdv]
      apply ih v hv hps
      exact (hprime.coprime_iff_not_dvd.mpr hdv).symm.dvd_of_dvd_mul_left hd

namespace PhysicalTree
/-- The same rectangular table which suffices for order stripping supplies
Euler's totient of every positive divisor of the group exponent. -/
theorem table_totient_exact {n N M m d : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hd : m∣M) (hd0 : 0 < d) (hdt : d∣m.totient) :
    totientScan (List.flatten (List.replicate n (tableFactors rows))) d=d.totient := by
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
  apply totientScan_exact _ d hd0
  · intro p hp
    obtain ⟨xs,hxs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hxs).2
    subst xs
    exact tableFactors_prime h p hp
  · rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
    exact hdt.trans hphi
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
