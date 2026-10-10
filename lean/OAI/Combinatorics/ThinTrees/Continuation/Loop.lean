import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Schedule
import OAI.Combinatorics.ThinTrees.Continuation.Start

namespace OAI

/-! Continuation loop. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

def advance (H : MultiGraph n m) (r : ℕ) (a : State n m) : State n m :=
  if a.scale^4 < (r:ℚ) then update H r (gain r) a else a

def stateAt (H : MultiGraph n m) (r i : ℕ) : State n m :=
  (advance H r)^[i] (initial H r)

def extractState (H : MultiGraph n m) (r : ℕ) : State n m :=
  stateAt H r (scheduleLength m r)

lemma stateAt_zero (H : MultiGraph n m) (r : ℕ) : stateAt H r 0=initial H r := rfl

lemma stateAt_succ (H : MultiGraph n m) (r i : ℕ) :
    stateAt H r (i+1)=advance H r (stateAt H r i) := Function.iterate_succ_apply' _ _ _

lemma active_scale_bound {a : State n m} {r : ℕ} (ha : 0 < (a.scale:ℝ))
    (hactive : a.scale^4 < (r:ℚ)) : (a.scale:ℝ) ≤ (r:ℝ)^(1/4:ℝ) := by
  rw [one_div,Real.le_rpow_inv_iff_of_pos ha.le (Nat.cast_nonneg _) (by norm_num : (0:ℝ)<4),Real.rpow_ofNat]
  exact_mod_cast hactive.le

lemma advance_quality (H : MultiGraph n m) (r : ℕ) (a : State n m) :
    (a.quality:ℝ)-2*(gain r:ℝ)*r*continuationStep m ≤ ((advance H r a).quality:ℝ) ∧
    ((advance H r a).quality:ℝ) ≤ (a.quality:ℝ) := by
  have hg : 0 ≤ (gain r:ℝ) := by simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]; positivity
  have ht := (continuation_parameters m).2.2.2.1
  have hc : 0 ≤ 2*(gain r:ℝ)*r*continuationStep m := by positivity
  unfold advance
  split_ifs <;> (try simp only [update,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,cast_stepQ]) <;>
    constructor <;> linarith only [hc]

lemma stateAt_quality (H : MultiGraph n m) (r i : ℕ) :
    (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) ≤ ((stateAt H r i).quality:ℝ) ∧
    ((stateAt H r i).quality:ℝ) ≤ r := by
  induction i with
  | zero => simp [stateAt_zero,initial]
  | succ i ih =>
    rw [stateAt_succ]
    have hh := advance_quality H r (stateAt H r i)
    push_cast
    constructor <;> nlinarith only [ih.1,ih.2,hh.1,hh.2]

lemma scale_dichotomy (H : MultiGraph n m) (r i : ℕ) :
    (r:ℚ) ≤ (stateAt H r i).scale^4 ∨
    (stateAt H r i).scale=(1+stepQ m)^i/2 := by
  induction i with
  | zero => exact Or.inr (by simp [stateAt_zero,initial])
  | succ i ih =>
    rw [stateAt_succ]
    rcases ih with ih|ih
    · exact Or.inl (by simpa only [advance,ite_eq_right (not_lt.mpr ih)] using ih)
    · by_cases ha : (stateAt H r i).scale^4 < (r:ℚ)
      · right
        rw [advance,ite_eq_left ha]
        simp only [update,ih]
        rw [pow_succ]
        ring
      · left
        simpa only [advance,ite_eq_right ha] using not_lt.mp ha

lemma extract_scale_bound (H : MultiGraph n m) (r : ℕ) (hr : 64^16 ≤ r)
    (hp : 0 < ((extractState H r).scale:ℝ)) :
    (r:ℝ)^(1/4:ℝ) ≤ ((extractState H r).scale:ℝ) := by
  obtain h|h := scale_dichotomy H r (scheduleLength m r)
  · rw [one_div,Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) hp.le (by norm_num : (0:ℝ)<4),Real.rpow_ofNat]
    exact_mod_cast h
  · have he : ((extractState H r).scale:ℝ)=(1+continuationStep m)^(scheduleLength m r)/2 := by
      simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,cast_stepQ,extractState] using congrArg (fun q : ℚ => (q:ℝ)) h
    rw [he]
    exact schedule_growth m r hr

theorem stateAt_invariant : ∃R : ℕ, 64^16 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      ∀i, i ≤ scheduleLength m r → Invariant H (stateAt H r i) := by
  obtain ⟨R,hR,hresponse⟩ := uniform_search_response
  refine ⟨max R (64^16),le_max_right _ _,?_⟩
  intro r hr n m H hn hpack i hi
  have hr0 : 0 < r := (by norm_num : 0 < 64^16).trans_le ((le_max_right _ _).trans hr)
  have hrlarge : 64^16 ≤ r := (le_max_right _ _).trans hr
  have hconn := packing_connected H hr0 hpack
  have hrm := packing_count_le_edges H hn hpack
  induction i with
  | zero => exact initial_invariant H (by omega) hr0 hpack
  | succ i ih =>
    have hii : i ≤ scheduleLength m r := by omega
    have ha := ih hii
    rw [stateAt_succ]
    by_cases hactive : (stateAt H r i).scale^4 < (r:ℚ)
    · rw [advance,ite_eq_left hactive]
      apply update_invariant H (by omega) hconn r (gain r) (stateAt H r i) ha
      apply hresponse r ((le_max_left _ _).trans hr) n m H hn hconn hrm
        (stateAt H r i).capacity (fun e => (ha.2.2.1 e).1) (fun e => (ha.2.2.1 e).2.1)
        (stateAt H r i).scale (stateAt H r i).quality (gain r) ha.1
        (active_scale_bound ha.1 hactive)
        ((running_quality_lower m r i hrlarge hii).trans (stateAt_quality H r i).1)
        (stateAt_quality H r i).2 (gain_bounds r hr0).1 (gain_bounds r hr0).2
        (large_gain r hrlarge) ha.2.2.2
    · simpa only [advance,ite_eq_right hactive] using ha

theorem extractState_correct : ∃R : ℕ, 64^16 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      Invariant H (extractState H r) ∧
      (r:ℝ)^(1/4:ℝ) ≤ ((extractState H r).scale:ℝ) ∧
      (1-4*(r:ℝ)^(-1/16:ℝ))*r ≤ ((extractState H r).quality:ℝ) ∧
      ((extractState H r).quality:ℝ) ≤ r := by
  obtain ⟨R,hR,hcorrect⟩ := stateAt_invariant
  refine ⟨R,hR,?_⟩
  intro r hr n m H hn hp
  have hi := hcorrect r hr n m H hn hp (scheduleLength m r) le_rfl
  have hr0 : 0 < r := (by norm_num : 0 < 64^16).trans_le (hR.trans hr)
  refine ⟨hi,extract_scale_bound H r (hR.trans hr) hi.1,?_,(stateAt_quality H r _).2⟩
  exact (running_quality_loss m r _ hr0 le_rfl).trans (stateAt_quality H r _).1

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
