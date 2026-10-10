import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityRootCount

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

lemma orbit_order_le (s m p : ℕ) [NeZero s] :
    orderOf (m : ZMod s) ≤ Nat.card (residueOrbit s m p) := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  let f : Fin (orderOf (m : ZMod s)) → residueOrbit s m p := fun i =>
    ⟨(m : ZMod s)^i.val, (Submonoid.mem_closure_pair _ _ _).mpr
      ⟨i.val,0,by simp⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact pow_injOn_Iio_orderOf i.isLt j.isLt (congrArg Subtype.val he)
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

lemma orbit_card_le {s m p : ℕ} [Fact s.Prime]
    (hm : (m : ZMod s) ≠ 0) (hp : (p : ZMod s) ≠ 0) :
    Nat.card (residueOrbit s m p) ≤ s-1 := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  have hn : ∀ x : residueOrbit s m p, x.val ≠ 0 := by
    intro x
    obtain ⟨u,v,huv⟩ := residueOrbit_rep x
    rw [← huv]
    exact_mod_cast mul_ne_zero (pow_ne_zero u hm) (pow_ne_zero v hp)
  let f : residueOrbit s m p → (ZMod s)ˣ := fun x => Units.mk0 x.val (hn x)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Units.val hxy
  simpa [Nat.card_eq_fintype_card, Nat.totient_prime (Fact.out : s.Prime)] using Fintype.card_le_of_injective f hf

/-- Pigeonhole collision in the square of side floor(sqrt |H|)+1. -/
lemma orbit_collision (s m p : ℕ) [NeZero s] :
    ∃ u v u' v' : ℕ,
      u ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      v ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      u' ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      v' ≤ Nat.sqrt (Nat.card (residueOrbit s m p)) ∧
      (u,v) ≠ (u',v') ∧
      ((m^u*p^v : ℕ) : ZMod s) = ((m^u'*p^v' : ℕ) : ZMod s) := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite _
  let q := Nat.sqrt (Nat.card (residueOrbit s m p))
  let f : Fin (q+1) × Fin (q+1) → residueOrbit s m p := fun x =>
    ⟨(m : ZMod s)^x.1.val*(p : ZMod s)^x.2.val,
      (Submonoid.mem_closure_pair _ _ _).mpr ⟨x.1.val,x.2.val,rfl⟩⟩
  have hb : Fintype.card (residueOrbit s m p) <
      Fintype.card (Fin (q+1) × Fin (q+1)) := by
    simpa [Fintype.card_prod, Nat.card_eq_fintype_card, q] using
      Nat.lt_succ_sqrt (Nat.card (residueOrbit s m p))
  obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hb
  refine ⟨a.1.val,a.2.val,b.1.val,b.2.val,
    Nat.le_of_lt_succ a.1.isLt,Nat.le_of_lt_succ a.2.isLt,
    Nat.le_of_lt_succ b.1.isLt,Nat.le_of_lt_succ b.2.isLt,?_,?_⟩
  · intro h
    apply hab
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact Fin.ext (congrArg Prod.snd h)
  · simpa [f] using congrArg Subtype.val he

lemma prime_factorization_positive {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime)
    (hqm : q ∣ m) : 0 < m.factorization q := by
  exact hq.factorization_pos_of_dvd hm hqm

/-- Distinct exponent pairs represent distinct natural numbers, using the other
prime divisor of m. This is where the perfect-power test is essential. -/
lemma exponent_pair_injective {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hqm : q ∣ m) (hpq : p ≠ q) :
    Function.Injective (fun uv : ℕ × ℕ => m^uv.1*p^uv.2) := by
  intro a b hab
  dsimp at hab
  have hfac := congrArg (fun k : ℕ => k.factorization q) hab
  have hpq0 : p.factorization q = 0 := by
    rw [hp.factorization]
    simp [hpq]
  simp only [Nat.factorization_mul (pow_ne_zero _ hm) (pow_ne_zero _ hp.ne_zero),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hpq0, mul_zero, add_zero] at hfac
  have hu : a.1 = b.1 := Nat.mul_right_cancel (prime_factorization_positive hm hq hqm) hfac
  have hv : a.2 = b.2 := by
    rw [hu] at hab
    have h := Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hm) _) hab
    exact Nat.pow_right_injective hp.two_le h
  exact Prod.ext hu hv

lemma exponent_bound {m p q u v : ℕ} (hm : 1 ≤ m) (hp : p ≤ m)
    (hu : u ≤ q) (hv : v ≤ q) : m^u*p^v ≤ m^(2*q) := by
  calc
    m^u*p^v ≤ m^q*m^q := Nat.mul_le_mul (Nat.pow_le_pow_right hm hu)
      ((Nat.pow_le_pow_left hp v).trans (Nat.pow_le_pow_right hm hv))
    _ = m^(2*q) := by rw [← pow_add]; congr 1; omega

/-- Elementary combinatorial bound used in the appendix. Pair the descending
factors M-i with c*(t-i), so no real logarithms or asymptotics are assumed. -/
lemma power_le_choose_mul {c s t : ℕ} (ht : t ≤ s) :
    c^t ≤ (c*s).choose t := by
  have hd : c^t * t.factorial ≤ (c*s).descFactorial t := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_prod_range]
    calc
      c^t * ∏ i ∈ Finset.range t, (t-i) =
          ∏ i ∈ Finset.range t, c*(t-i) := by simp [Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ Finset.range t, (c*s-i) := by
        apply Finset.prod_le_prod
        intro i hi
        have hi' := Finset.mem_range.mp hi
        by_cases hc : c = 0
        · simp [hc]
        · have hc' : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc
          rw [Nat.mul_sub_left_distrib]
          have hct : c*t ≤ c*s := Nat.mul_le_mul_left c ht
          have hci : i ≤ c*i := Nat.le_mul_of_pos_left i (by omega)
          omega
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hd
  exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_comm] using hd) (Nat.factorial_pos t)

end ExactQuantumFactoring.Primality


end

end OAI
