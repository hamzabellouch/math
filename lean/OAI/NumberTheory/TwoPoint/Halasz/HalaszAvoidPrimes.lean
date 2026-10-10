import OAI.NumberTheory.TwoPoint.Halasz.HalaszDistinctMoment
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Dist

namespace OAI

/-! A small family of primes contains a prime preserving distinctness
of both long tuples. Only the prime supply is analytic. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_large_prime_divisors {L r m : ℕ} (hL : 0<L) (hm : 0<m)
    (hbound : m<L^r) (P : Finset ℕ)
    (hP : ∀ p∈P, p.Prime ∧ L≤p) :
    (P.filter (fun p => p∣m)).card<r := by
  let D := P.filter (fun p => p∣m)
  have hsub : D⊆m.primeFactors := by
    intro p hp
    obtain ⟨hpP,hpm⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hP p hpP).1,hpm,hm.ne'⟩
  have hdvd : (∏ p∈D, p)∣m :=
    (prod_dvd_prod_of_subset D m.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd m)
  have hprod : L^D.card≤∏ p∈D, p := by
    calc
      L^D.card = ∏ _p∈D, L := by simp
      _ ≤ ∏ p∈D, p := prod_le_prod (fun p hp => (hP p (mem_filter.mp hp).1).2)
  by_contra! hn
  change r≤D.card at hn
  have hpow : L^r≤L^D.card := Nat.pow_le_pow_right hL hn
  have hle := Nat.le_of_dvd hm hdvd
  exact (not_lt_of_ge (hpow.trans (hprod.trans hle))) hbound

lemma halasz_congruent_prime_count {L r N : ℕ} (hL : 0<L) (hN : N≤L^r)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ L≤p)
    (a b : Fin N) (hab : a≠b) :
    (P.filter (fun p => (((a.val+1:ℕ):ZMod p)=((b.val+1:ℕ):ZMod p)))).card≤r := by
  let m := Nat.dist (a.val+1) (b.val+1)
  have hm : 0<m := Nat.dist_pos_of_ne (fun h => hab (Fin.ext (by omega)))
  have hmN : m<N := by dsimp [m,Nat.dist]; have := a.isLt; have := b.isLt; omega
  have hd := halasz_large_prime_divisors hL hm (hmN.trans_le hN) P hP
  apply le_trans _ hd.le
  apply card_le_card
  intro p hp
  obtain ⟨hp,hcong⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hp,?_⟩
  have hmod := (ZMod.natCast_eq_natCast_iff (a.val+1) (b.val+1) p).mp hcong
  change p∣Nat.dist (a.val+1) (b.val+1)
  rcases le_total (a.val+1) (b.val+1) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact (Nat.modEq_iff_dvd' h).mp hmod
  · rw [Nat.dist_eq_sub_of_le_right h]
    exact (Nat.modEq_iff_dvd' h).mp hmod.symm

theorem halasz_bad_residue_prime_count {L r N ℓ : ℕ} (hL : 0<L) (hN : N≤L^r)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ L≤p)
    (x : Fin ℓ → Fin N) (hx : Function.Injective x) :
    (P.filter (fun p => ¬Function.Injective
      (fun i => (((x i).val+1:ℕ):ZMod p)))).card≤ℓ^2*r := by
  let I := (univ : Finset (Fin ℓ × Fin ℓ)).filter (fun ij => ij.1≠ij.2)
  let B := fun ij : Fin ℓ × Fin ℓ => P.filter (fun p =>
    ((((x ij.1).val+1:ℕ):ZMod p)=(((x ij.2).val+1:ℕ):ZMod p)))
  have hsub : (P.filter (fun p => ¬Function.Injective
      (fun i => (((x i).val+1:ℕ):ZMod p))))⊆I.biUnion B := by
    intro p hp
    obtain ⟨hpP,hbad⟩ := mem_filter.mp hp
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hbad
    exact mem_biUnion.mpr ⟨(i,j),mem_filter.mpr ⟨mem_univ _,hne⟩,
      mem_filter.mpr ⟨hpP,hij⟩⟩
  have hI : I.card≤ℓ^2 := by
    calc
      I.card ≤ (univ : Finset (Fin ℓ × Fin ℓ)).card := card_filter_le _ _
      _ = ℓ^2 := by simp [pow_two]
  calc
    _ ≤ (I.biUnion B).card := card_le_card hsub
    _ ≤ I.card*r := card_biUnion_le_card_mul I B r (fun ij hij =>
      halasz_congruent_prime_count hL hN P hP _ _ (fun h => (mem_filter.mp hij).2 (hx h)))
    _ ≤ ℓ^2*r := Nat.mul_le_mul_right _ hI

theorem halasz_exists_good_prime {L r N ℓ : ℕ} (hL : 0<L) (hN : N≤L^r)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ L≤p) (hcard : 2*(ℓ^2*r)<P.card)
    (x y : Fin ℓ → Fin N) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ p∈P, Function.Injective (fun i => (((x i).val+1:ℕ):ZMod p)) ∧
      Function.Injective (fun i => (((y i).val+1:ℕ):ZMod p)) := by
  let Bx := P.filter (fun p => ¬Function.Injective (fun i => (((x i).val+1:ℕ):ZMod p)))
  let By := P.filter (fun p => ¬Function.Injective (fun i => (((y i).val+1:ℕ):ZMod p)))
  by_contra! hn
  have hsub : P⊆Bx∪By := by
    intro p hp
    by_cases hxp : Function.Injective (fun i => (((x i).val+1:ℕ):ZMod p))
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hn p hp hxp⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,hxp⟩)
  have hbX := halasz_bad_residue_prime_count hL hN P hP x hx
  have hbY := halasz_bad_residue_prime_count hL hN P hP y hy
  have hbad := (card_le_card hsub).trans (card_union_le Bx By)
  change P.card≤Bx.card+By.card at hbad
  change Bx.card≤ℓ^2*r at hbX
  change By.card≤ℓ^2*r at hbY
  omega

end TwoPointCorrelations

end OAI
