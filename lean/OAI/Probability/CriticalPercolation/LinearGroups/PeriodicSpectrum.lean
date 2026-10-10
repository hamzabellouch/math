import Mathlib

namespace OAI

section
noncomputable section
open Polynomial Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma multiset_prod_dvd_pow_card {R : Type*} [CommMonoid R] (s : Multiset R) (a : R)
    (h : ∀ b∈s, b∣a) : s.prod∣a^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    simp only [Multiset.prod_cons,Multiset.card_cons,pow_succ']
    exact mul_dvd_mul (h b (Multiset.mem_cons_self _ _))
      (ih (fun c hc => h c (Multiset.mem_cons_of_mem hc)))

lemma nilpotent_aeval_of_vanishing_roots {K R : Type*} [Field K] [Ring R] [Algebra K R]
    (a : R) (hp : (minpoly K a).Monic) (hs : (minpoly K a).Splits)
    (q : K[X]) (hq : ∀ x ∈ (minpoly K a).roots, q.IsRoot x) : IsNilpotent (aeval a q) := by
  have hd : minpoly K a ∣ q^(minpoly K a).roots.card := by
    nth_rw 1 [hs.eq_prod_roots_of_monic hp]
    convert multiset_prod_dvd_pow_card ((minpoly K a).roots.map (fun x => X-C x)) q ?_ using 1
    · simp only [Multiset.card_map]
    · intro b hb
      obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hb
      exact dvd_iff_isRoot.mpr (hq x hx)
  exact ⟨_,by rw [←map_pow]; exact minpoly.dvd_iff.mp hd⟩

lemma exists_scalar_unipotent_power {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : End K V) (a : K) (ha : a≠0)
    (hr : ∀ r, (minpoly K A).IsRoot r → ∃ m : ℕ, 0 < m ∧ (r/a)^m=1) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (A^m-a^m • (1:End K V)) := by
  let s := (minpoly K A).roots.toFinset
  have he (r : s) : ∃ m : ℕ, 0 < m ∧ (r.val/a)^m=1 :=
    hr r.val (isRoot_of_mem_roots (Multiset.mem_toFinset.mp r.property))
  choose m hm hm1 using he
  let N := ∏ r : s, m r
  have hN : 0 < N := Finset.prod_pos (fun r _ => hm r)
  have hpow (r : s) : (r.val/a)^N=1 := by
    have hd : m r∣N := Finset.dvd_prod_of_mem m (Finset.mem_univ r)
    obtain ⟨k,hk⟩ := hd
    rw [hk,pow_mul,hm1 r,one_pow]
  refine ⟨N,hN,?_⟩
  have hn := nilpotent_aeval_of_vanishing_roots A (minpoly.monic (Algebra.IsIntegral.isIntegral A))
    (IsAlgClosed.splits (minpoly K A)) (X^N-C (a^N)) ?_
  · simpa only [map_sub,map_pow,aeval_X,aeval_C,Algebra.algebraMap_eq_smul_one,_root_.smul_pow,one_pow] using hn
  · intro r hr'
    have hrN := hpow ⟨r,Multiset.mem_toFinset.mpr hr'⟩
    have hep : r^N=a^N := by
      apply (div_eq_one_iff_eq (pow_ne_zero _ ha)).mp
      simpa only [div_pow] using hrN
    simp only [IsRoot,eval_sub,eval_pow,eval_X,eval_C,hep,sub_self]

end CriticalPercolation.LinearGrowth
end
end

end OAI
