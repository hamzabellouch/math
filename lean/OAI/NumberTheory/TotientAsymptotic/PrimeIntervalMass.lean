import OAI.NumberTheory.TotientAsymptotic.PrimeBox
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! Endpoint bookkeeping for reciprocal primes in half-open intervals. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime

private def primesBelow (x : ℝ) : Finset ℕ :=
  (primesUpTo x).filter (fun p => (p : ℝ)<x)

def primeReciprocalLE (x : ℝ) : ℝ := ∑ p ∈ primesUpTo x, (p : ℝ)⁻¹

def primeReciprocalLT (x : ℝ) : ℝ := ∑ p ∈ primesBelow x, (p : ℝ)⁻¹

private lemma mem_primesUpTo {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p ∈ primesUpTo x ↔ p.Prime ∧ (p : ℝ)≤x := by
  simp only [primesUpTo,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hp⟩,hprime⟩
    exact ⟨hprime,(Nat.le_floor_iff hx).mp hp⟩
  · rintro ⟨hprime,hp⟩
    exact ⟨⟨hprime.two_le,(Nat.le_floor_iff hx).mpr hp⟩,hprime⟩

private lemma mem_primesBelow {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p ∈ primesBelow x ↔ p.Prime ∧ (p : ℝ)<x := by
  simp only [primesBelow,Finset.mem_filter,mem_primesUpTo hx]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.le⟩,h.2⟩⟩

lemma primeReciprocal_endpoint_error {x : ℝ} (hx : 0<x) :
    |primeReciprocalLT x-primeReciprocalLE x| ≤ 1/x := by
  classical
  have hsub : primesBelow x⊆primesUpTo x := Finset.filter_subset _ _
  let K := primesUpTo x\primesBelow x
  have hK (p : ℕ) (hp : p∈K) : (p : ℝ)=x := by
    obtain ⟨hpU,hpL⟩ := Finset.mem_sdiff.mp hp
    have hp1 := (mem_primesUpTo hx.le).mp hpU
    have hp2 : ¬(p : ℝ)<x := by
      intro hh
      exact hpL ((mem_primesBelow hx.le).mpr ⟨hp1.1,hh⟩)
    exact le_antisymm hp1.2 (le_of_not_gt hp2)
  have hsum : (∑ p ∈ K, (p : ℝ)⁻¹)≤1/x := by
    by_cases hne : K.Nonempty
    · obtain ⟨p,hp⟩ := hne
      have heq : K={p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hp,?_⟩
        intro q hq
        exact_mod_cast (hK q hq).trans (hK p hp).symm
      simp only [heq,Finset.sum_singleton,hK p hp,one_div]
      rfl
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
      positivity
  have heq : primeReciprocalLE x-primeReciprocalLT x=∑ p ∈ K, (p : ℝ)⁻¹ := by
    exact (Finset.sum_sdiff_eq_sub hsub).symm
  have hnon : 0≤∑ p ∈ K, (p : ℝ)⁻¹ := Finset.sum_nonneg (by intros; positivity)
  rw [abs_sub_comm,heq,abs_of_nonneg hnon]
  exact hsum

lemma unitPrimeBox_reciprocal (m : ℕ) :
    (∑ p ∈ unitPrimeBox m, (p : ℝ)⁻¹)=
      primeReciprocalLT (Real.exp (Real.exp (m : ℝ)))-
      primeReciprocalLT (Real.exp (Real.exp ((m : ℝ)-1))) := by
  classical
  let a := Real.exp (Real.exp ((m : ℝ)-1))
  let b := Real.exp (Real.exp (m : ℝ))
  have ha : 0<a := Real.exp_pos _
  have hb : 0<b := Real.exp_pos _
  have hab : a≤b := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have hsub : primesBelow a⊆primesBelow b := by
    intro p hp
    have hh := (mem_primesBelow ha.le).mp hp
    exact (mem_primesBelow hb.le).mpr ⟨hh.1,hh.2.trans_le hab⟩
  have hset : unitPrimeBox m=primesBelow b\primesBelow a := by
    ext p
    simp only [unitPrimeBox,Finset.mem_filter,Finset.mem_Icc,Finset.mem_sdiff,
      mem_primesBelow ha.le,mem_primesBelow hb.le]
    constructor
    · rintro ⟨⟨_,_⟩,hp,hal,hbl⟩
      exact ⟨⟨hp,hbl⟩,fun hh => (not_lt_of_ge hal) hh.2⟩
    · rintro ⟨⟨hp,hpb⟩,hpa⟩
      have hpa' : a≤(p : ℝ) := le_of_not_gt (fun hh => hpa ⟨hp,hh⟩)
      refine ⟨⟨hp.two_le,?_⟩,hp,hpa',hpb⟩
      apply (Nat.cast_le (α := ℝ)).mp
      exact hpb.le.trans (Nat.le_ceil b)
  rw [hset,Finset.sum_sdiff_eq_sub hsub]
  rfl

end TotientAsymptotic

end

end OAI
