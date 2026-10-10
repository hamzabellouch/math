import OAI.NumberTheory.Ostmann.Construction.TransformReversal

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem prime_divisor_list_gt (s : ℕ) (xs : List ℕ)
    (hxs : ∀x∈xs,Nat.Prime x ∧ s<x) (q : ℕ) (hq : Nat.Prime q) (hd : q∣xs.prod) : s<q := by
  induction xs with
  | nil => exact (hq.not_dvd_one hd).elim
  | cons x xs ih =>
    rcases hq.dvd_mul.mp hd with hdx|hdxs
    · have heq : q=x := (Nat.prime_dvd_prime_iff_eq hq (hxs x (List.mem_cons_self)).1).mp hdx
      subst q
      exact (hxs x (List.mem_cons_self)).2
    · exact ih (fun z hz => hxs z (List.mem_cons_of_mem x hz)) hdxs

theorem reversal_halves_coprime (P Hp Hm : ℕ) (v w s : ℤ)
    (hs : s≠0) (hP : Hp.Coprime P)
    (hlarge : ∀q,Nat.Prime q→q∣Hp→s.natAbs<q)
    (heq : Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)=s*(P:ℤ)) : Hp.Coprime Hm := by
  by_contra hn
  obtain ⟨q,hq,hqp,hqm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  exact no_large_common_divisor heq hs (hlarge q hq hqp)
    ((hP.of_dvd_left hqp).isCoprime)
    ⟨by exact_mod_cast hqp,by exact_mod_cast hqm⟩

theorem reversal_sample_halves_coprime (P qp qm : ℕ) (hp hm : List SmallSlot) (v w s : ℤ)
    (hs : s≠0) (hqp : Nat.Prime qp) (hsmall : ∀q∈hp,Nat.Prime q.value)
    (hP : (halfProduct qp hp).Coprime P)
    (hlarge : s.natAbs<qp ∧ ∀q∈hp,s.natAbs<q.value)
    (heq : Arithmetic.reversalNumerator v w (halfProduct qp hp:ℤ) (halfProduct qm hm:ℤ)=s*(P:ℤ)) :
    (halfProduct qp hp).Coprime (halfProduct qm hm) := by
  apply reversal_halves_coprime P _ _ v w s hs hP _ heq
  intro q hq hd
  apply prime_divisor_list_gt s.natAbs (qp::hp.map SmallSlot.value) _ q hq hd
  intro z hz
  rcases List.mem_cons.mp hz with he|hz
  · subst z
    exact ⟨hqp,hlarge.1⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact ⟨hsmall a ha,hlarge.2 a ha⟩

end Ostmann.Construction

end

end OAI
