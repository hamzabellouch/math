import Mathlib

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- One occurrence of the source's prime-stripping loop. A repeated prime
factor list supplies exactly as many attempts as its known multiplicity. -/
def stripOrderPrime {G : Type*} [Monoid G] [DecidableEq G] (a : G) (q v : ℕ) : ℕ :=
  if q ∣ v ∧ a^(v/q)=1 then v/q else v

def stripOrderFactors {G : Type*} [Monoid G] [DecidableEq G] (a : G) : List ℕ→ℕ→ℕ
  | [], v => v
  | q::qs, v => stripOrderFactors a qs (stripOrderPrime a q v)

lemma stripOrderPrime_multiple {G : Type*} [Monoid G] [DecidableEq G]
    (a : G) (hr : 0 < orderOf a) (q k : ℕ) :
    stripOrderPrime a q (orderOf a*k)=orderOf a*(if q∣k then k/q else k) := by
  let r := orderOf a
  have hcond : (q∣r*k ∧ a^((r*k)/q)=1) ↔ q∣k := by
    constructor
    · rintro ⟨hq,hpow⟩
      have h := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hh : r*q∣r*k := by simpa only [Nat.mul_comm q] using (Nat.dvd_div_iff_mul_dvd hq).mp h
      exact (Nat.mul_dvd_mul_iff_left hr).mp hh
    · intro hk
      refine ⟨hk.mul_left r,?_⟩
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [Nat.mul_div_assoc r hk]
      exact dvd_mul_right r (k/q)
  change (if q∣r*k ∧ a^((r*k)/q)=1 then (r*k)/q else r*k)=_
  simp only [hcond]
  split_ifs with hq
  · exact Nat.mul_div_assoc r hq
  · rfl

lemma quotient_dvd_tail {k q v : ℕ} (hq : 0 < q) (hk : q∣k) (hkv : k∣q*v) : k/q ∣ v := by
  obtain ⟨c,hc⟩ := hkv
  refine ⟨c,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hq
  rw [← Nat.mul_assoc,Nat.mul_div_cancel' hk]
  exact hc

/-- Complete factor stripping: no excess prime can survive a scan of a known
factorization of a multiple of the initial quotient. There is no call to an
order oracle in this algorithm. -/
theorem stripOrderFactors_exact {G : Type*} [Monoid G] [DecidableEq G]
    (a : G) (hr : 0 < orderOf a) (qs : List ℕ)
    (hp : ∀ q∈qs, q.Prime) (k : ℕ) (hk : k∣qs.prod) :
    stripOrderFactors a qs (orderOf a*k)=orderOf a := by
  induction qs generalizing k with
  | nil =>
    have he : k=1 := Nat.dvd_one.mp hk
    simp [stripOrderFactors,he]
  | cons q qs ih =>
    have hq := hp q (by simp)
    have htail : ∀ p∈qs, p.Prime := fun p hh => hp p (by simp [hh])
    simp only [stripOrderFactors,stripOrderPrime_multiple a hr]
    apply ih htail
    by_cases hdiv : q∣k
    · rw [ite_eq_left hdiv]
      exact quotient_dvd_tail hq.pos hdiv hk
    · rw [ite_eq_right hdiv]
      exact (hq.coprime_iff_not_dvd.mpr hdiv).symm.dvd_of_dvd_mul_left hk

/-- Specializing to the known factorization of phi(m), as in source §5. The
factor list is explicit input produced by the completed auxiliary tree. -/
theorem strip_totient_factors {m : ℕ} (hm : 2 ≤ m) (a : (ZMod m)ˣ)
    (qs : List ℕ) (hp : ∀ q∈qs,q.Prime) (hprod : qs.prod=m.totient) :
    stripOrderFactors a qs m.totient=orderOf a := by
  let : NeZero m := ⟨by omega⟩
  have hd : orderOf a ∣ m.totient := by simpa [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using orderOf_dvd_natCard a
  have hr : 0 < orderOf a := orderOf_pos a
  have he := Nat.mul_div_cancel' hd
  have hq : m.totient/orderOf a ∣ qs.prod := by
    rw [hprod]
    exact (dvd_mul_left (m.totient/orderOf a) (orderOf a)).trans (dvd_of_eq he)
  rw [← he]
  exact stripOrderFactors_exact a hr qs hp _ hq

end ExactQuantumFactoring


end

end OAI
