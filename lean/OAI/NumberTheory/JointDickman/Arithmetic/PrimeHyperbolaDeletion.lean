import OAI.NumberTheory.JointDickman.Arithmetic.TruncatedPrimeHyperbola

namespace OAI

/-! # Exact small-variable deletion for a prime hyperbola -/
namespace JointDickman
open Finset

lemma prime_hyperbola_small_m_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (N Z : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (min Z (N/p)), G p m) =
      ∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), G p m := by
  have he (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      (Ioc 0 (min Z (N/p))) = (Ioc 0 Z).filter (fun m => p*m ≤ N) := by
    ext m
    simp only [mem_Ioc,mem_filter,le_min_iff]
    have hp0 := (Nat.mem_primesLE.mp hp).2.pos
    constructor
    · rintro ⟨hm0,hmZ,hmN⟩
      exact ⟨⟨hm0,hmZ⟩,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hp0).mp hmN⟩
    · rintro ⟨⟨hm0,hmZ⟩,hmN⟩
      exact ⟨hm0,hmZ,(Nat.le_div_iff_mul_le hp0).mpr (by simpa [mul_comm] using hmN)⟩
  calc
    _ = ∑ p ∈ Nat.primesLE N, ∑ m ∈ (Ioc 0 Z).filter (fun m => p*m ≤ N), G p m := by
      apply sum_congr rfl
      intro p hp
      rw [he p hp]
    _ = ∑ m ∈ Ioc 0 Z, ∑ p ∈ (Nat.primesLE N).filter (fun p => p*m ≤ N), G p m := by
      simp_rw [sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      congr 1
      ext p
      simp only [mem_filter,Nat.mem_primesLE]
      have hm0 := (mem_Ioc.mp hm).1
      constructor
      · rintro ⟨⟨hpN,hp⟩,hprod⟩
        exact ⟨(Nat.le_div_iff_mul_le hm0).mpr hprod,hp⟩
      · rintro ⟨hpM,hp⟩
        exact ⟨⟨hpM.trans (Nat.div_le_self N m),hp⟩,(Nat.le_div_iff_mul_le hm0).mp hpM⟩

lemma interval_sum_small_large {R : Type*} [AddCommMonoid R]
    (G : ℕ → R) (M Z : ℕ) :
    (∑ m ∈ Ioc 0 M, G m) =
      (∑ m ∈ Ioc 0 (min Z M), G m) + ∑ m ∈ Ioc Z M, G m := by
  have he : Ioc (min Z M) M = Ioc Z M := by
    ext m
    simp only [mem_Ioc]
    omega
  rw [←he]
  exact (sum_Ioc_consecutive G (Nat.zero_le _) (min_le_right Z M)).symm

lemma prime_hyperbola_split {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (N Z : ℕ) (hZN : Z ≤ N) (hZ : 0 < Z) :
    (∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p), G p m) =
      (∑ p ∈ Nat.primesLE Z, ∑ m ∈ Ioc 0 (N/p), G p m) +
      (∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), if Z < p then G p m else 0) +
      ∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z < p),
        ∑ m ∈ Ioc Z (N/p), G p m := by
  classical
  let P := (Nat.primesLE N).filter (fun p => Z < p)
  have hsmall : (Nat.primesLE N).filter (fun p => ¬ Z < p) = Nat.primesLE Z := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,not_lt]
    constructor
    · rintro ⟨⟨hpN,hp⟩,hpZ⟩
      exact ⟨hpZ,hp⟩
    · rintro ⟨hpZ,hp⟩
      exact ⟨⟨hpZ.trans hZN,hp⟩,hpZ⟩
  have hs := sum_filter_add_sum_filter_not (Nat.primesLE N) (fun p => Z < p)
    (fun p => ∑ m ∈ Ioc 0 (N/p), G p m)
  rw [hsmall] at hs
  have hsplit : (∑ p ∈ P, ∑ m ∈ Ioc 0 (N/p), G p m) =
      (∑ p ∈ P, ∑ m ∈ Ioc 0 (min Z (N/p)), G p m) +
      ∑ p ∈ P, ∑ m ∈ Ioc Z (N/p), G p m := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    exact interval_sum_small_large (G p) (N/p) Z
  have hfirst : (∑ p ∈ P, ∑ m ∈ Ioc 0 (min Z (N/p)), G p m) =
      ∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), if Z < p then G p m else 0 := by
    rw [←prime_hyperbola_small_m_reindex]
    dsimp [P]
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> simp
  have htail : (∑ p ∈ P, ∑ m ∈ Ioc Z (N/p), G p m) =
      ∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z < p), ∑ m ∈ Ioc Z (N/p), G p m := by
    symm
    apply sum_subset
    · intro p hp
      obtain ⟨hpNZ,hpZ⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
        ⟨(Nat.mem_primesLE.mp hpNZ).1.trans (Nat.div_le_self N Z),(Nat.mem_primesLE.mp hpNZ).2⟩,hpZ⟩
    · intro p hp hn
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      have hlarge : N/Z < p := by
        by_contra h
        apply hn
        exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hprime⟩,(mem_filter.mp hp).2⟩
      have hNp : N/p ≤ Z := by
        by_contra hnZ
        have hh := (Nat.le_div_iff_mul_le hprime.pos).mp (show Z+1 ≤ N/p by omega)
        have hpZ : N < p*Z := (Nat.div_lt_iff_lt_mul hZ).mp hlarge
        nlinarith
      have hempty : Ioc Z (N/p) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        have hh := mem_Ioc.mp hm
        omega
      rw [hempty,sum_empty]
  rw [←hs]
  change _ = _
  rw [show (∑ p ∈ (Nat.primesLE N).filter (fun p => Z < p), ∑ m ∈ Ioc 0 (N/p), G p m) =
    (∑ p ∈ P, ∑ m ∈ Ioc 0 (N/p), G p m) from rfl,hsplit,hfirst,htail]
  ac_rfl

end JointDickman

end OAI
