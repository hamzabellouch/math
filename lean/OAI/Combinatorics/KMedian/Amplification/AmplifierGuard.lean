import Mathlib
import OAI.Combinatorics.KMedian.Amplification.AmplifierIteration
import OAI.Combinatorics.KMedian.Machines.IterationPolynomial

namespace OAI

section Inline_PCPAmplifierGuard
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

abbrev State := ℕ × (ℕ × CSPTable Label)
noncomputable def guarded (s : State) : State :=
  (s.1,if s.2.1≤ s.1 then (2*s.2.1,next s.2.2) else s.2)
lemma poly_guarded : Poly guarded := by
  unfold guarded
  apply Poly.pair Poly.fst
  apply Poly.ite_prop
  · fun_prop
  · exact Poly.pair (by fun_prop) (poly_next.comp (Poly.snd.comp Poly.snd))
  · exact Poly.snd
noncomputable def schedule (s : CSPTable Label) (i : ℕ) : State :=
  (s.2.length,(2^(min i (Nat.log 2 s.2.length+1)),iterate (min i (Nat.log 2 s.2.length+1)) s))
lemma schedule_zero (s : CSPTable Label) : schedule s 0=(s.2.length,(1,s)) := by
  simp only [schedule,Nat.zero_min,pow_zero,iterate]
lemma schedule_succ (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    guarded (schedule s i)=schedule s (i+1) := by
  let n := Nat.log 2 s.2.length+1
  have guard (j : ℕ) : 2^j≤ s.2.length ↔ j<n :=
    (Nat.le_log_iff_pow_le (by omega : 1<2) (Nat.ne_of_gt h.1)).symm.trans Nat.lt_add_one_iff.symm
  by_cases hi : i<n
  · have h0 : min i n=i := min_eq_left hi.le
    have h1 : min (i+1) n=i+1 := min_eq_left hi
    have ht := (guard i).mpr hi
    change (s.2.length,if 2^(min i n)≤ s.2.length then _ else _)=_
    simp only [h0,ite_eq_left ht,schedule,show Nat.log 2 s.2.length+1=n from rfl,h1,iterate,pow_succ']
  · have h0 : min i n=n := min_eq_right (by omega)
    have h1 : min (i+1) n=n := min_eq_right (by omega)
    have ht : ¬2^n≤ s.2.length := by rw [guard]; exact lt_irrefl _
    change (s.2.length,if 2^(min i n)≤ s.2.length then _ else _)=_
    simp only [h0,ite_eq_right ht,schedule,show Nat.log 2 s.2.length+1=n from rfl,h1]
lemma guarded_iterate (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    guarded^[i] (s.2.length,(1,s))=schedule s i := by
  have hh := Expander.iterate_sequence guarded (schedule s) (schedule_succ s h) i
  rwa [schedule_zero] at hh
lemma schedule_valid (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    (schedule s i).2.2.WellFormed := iterate_valid h _
lemma schedule_count (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    (schedule s i).2.2.1.length+(schedule s i).2.2.2.length≤
      co*(s.2.length^co*(s.1.length+s.2.length)) := by
  have hc : 1≤co := co_pos
  apply (iterate_count h _).trans
  have hpow := Nat.pow_le_pow_right hc (min_le_right i (Nat.log 2 s.2.length+1))
  have hb := log_power_bound co s.2.length h.1
  calc
    _ ≤ co^(Nat.log 2 s.2.length+1)*(s.1.length+s.2.length) := Nat.mul_le_mul_right _ hpow
    _ = co*(co^(Nat.log 2 s.2.length)*(s.1.length+s.2.length)) := by rw [pow_succ',Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)
lemma schedule_counter (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    (schedule s i).2.1≤2*s.2.length := by
  change 2^(min i (Nat.log 2 s.2.length+1))≤_
  calc
    _ ≤ 2^(Nat.log 2 s.2.length+1) := Nat.pow_le_pow_right (by omega) (min_le_right _ _)
    _ = 2*2^(Nat.log 2 s.2.length) := pow_succ' _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (Nat.ne_of_gt h.1))
noncomputable def generate (s : CSPTable Label) : CSPTable Label :=
  (guarded^[(normalize s).2.length+1] ((normalize s).2.length,(1,normalize s))).2.2
lemma generate_eq (s : CSPTable Label) :
    generate s=iterate (Nat.log 2 (normalize s).2.length+1) (normalize s) := by
  rw [generate,guarded_iterate _ (normalize_valid s)]
  change iterate (min _ _) _=_
  rw [min_eq_right]
  exact Nat.add_le_add_right (Nat.log_le_self 2 _) 1
lemma generate_valid (s : CSPTable Label) : (generate s).WellFormed := by
  rw [generate_eq]
  exact iterate_valid (normalize_valid s) _
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierGuard

end OAI
