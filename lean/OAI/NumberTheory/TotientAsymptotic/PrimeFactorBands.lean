import OAI.NumberTheory.TotientAsymptotic.ComparisonSizes
import OAI.NumberTheory.TotientAsymptotic.NormalityIntervals
import Mathlib.Data.Nat.Squarefree

namespace OAI

/-! Exact arithmetic of the prime-factor bands in Ford's collision argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def partBetween (n : ℕ) (U V : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)).prod

lemma partBelow_pos (n : ℕ) (V : ℝ) : 0 < partBelow n V := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

lemma partBetween_pos (n : ℕ) (U V : ℝ) : 0 < partBetween n U V := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

lemma partBelow_factors (n : ℕ) (V : ℝ) :
    (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).Perm (partBelow n V).primeFactorsList := by
  apply Nat.primeFactorsList_unique rfl
  intro p hp
  exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1

lemma partBetween_factors (n : ℕ) (U V : ℝ) :
    (n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)).Perm
      (partBetween n U V).primeFactorsList := by
  apply Nat.primeFactorsList_unique rfl
  intro p hp
  exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1

lemma partBetween_omega (n : ℕ) (U V : ℝ) :
    (partBetween n U V).primeFactorsList.length=omegaIn n U V :=
  (partBetween_factors n U V).length_eq.symm

lemma partBelow_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (V : ℝ) :
    partBelow (n*m) V=partBelow n V*partBelow m V := by
  have hh := (Nat.perm_primeFactorsList_mul hn hm).filter (fun p : ℕ => decide ((p:ℝ) ≤ V))
  simpa [partBelow,List.filter_append,List.prod_append] using hh.prod_eq

lemma partBetween_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (U V : ℝ) :
    partBetween (n*m) U V=partBetween n U V*partBetween m U V := by
  have hh := (Nat.perm_primeFactorsList_mul hn hm).filter
    (fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))
  simpa [partBetween,List.filter_append,List.prod_append] using hh.prod_eq

lemma partBelow_band_split (n : ℕ) {U V : ℝ} (hUV : U ≤ V) :
    partBelow n U*partBetween n U V=partBelow n V := by
  have hh := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => (p:ℝ) ≤ U) id
    (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V))
  have hleft : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => (p:ℝ) ≤ U)=n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ U) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    by_cases h : (p:ℝ) ≤ U
    · simp [h,h.trans hUV]
    · simp [h]
  have hright : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => ¬(p:ℝ) ≤ U)=
      n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    simp [not_le]
  simpa only [List.map_id,hleft,hright,partBelow,partBetween] using hh

lemma partBetween_dvd {n : ℕ} (hn : n ≠ 0) (U V : ℝ) : partBetween n U V ∣ n := by
  have hh := (List.filter_sublist (p:=fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))
    (l:=n.primeFactorsList)).prod_dvd_prod
  obtain ⟨c,hc⟩ := hh
  exact ⟨c,by simpa only [partBetween,Nat.prod_primeFactorsList hn] using hc⟩

lemma partBetween_squarefree {n : ℕ} (hn : n ≠ 0) {U V : ℝ}
    (hsq : SquarefreeAbove n U) : Squarefree (partBetween n U V) := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hpband : p ∈ (partBetween n U V).primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd (partBetween_pos n U V).ne' hp).mpr
      ((dvd_mul_right p p).trans hd)
  have hpf := (partBetween_factors n U V).mem_iff.mpr hpband
  have hbound : U < (p:ℝ) ∧ (p:ℝ) ≤ V := of_decide_eq_true (List.mem_filter.mp hpf).2
  have hpU := hbound.1
  apply hsq p hp hpU
  simpa only [pow_two] using hd.trans (partBetween_dvd hn U V)

end TotientAsymptotic

end

end OAI
