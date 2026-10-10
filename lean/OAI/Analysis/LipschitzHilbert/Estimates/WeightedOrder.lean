import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI

/-!
# Finite size-biased random orders

The recursive expectation below chooses the next element proportionally to its
positive weight. This gives the same first-arrival probabilities as independent
exponential clocks, while keeping the probability space entirely finite.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι : Type*} [DecidableEq ι]

def orderMass (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, w i

def orderAverage (w : ι → ℝ) (s : Finset ι) (f : List ι → ℝ) : ℝ :=
  if _hs : s.Nonempty then
    ∑ i : s, w i / orderMass w s *
      orderAverage w (s.erase i.val) (fun l => f (i.val :: l))
  else f []
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem i.property

theorem orderAverage_empty (w : ι → ℝ) (f : List ι → ℝ) :
    orderAverage w ∅ f = f [] := by
  rw [orderAverage]
  simp

theorem orderAverage_nonempty (w : ι → ℝ) (s : Finset ι)
    (hs : s.Nonempty) (f : List ι → ℝ) :
    orderAverage w s f = ∑ i : s, w i / orderMass w s *
      orderAverage w (s.erase i.val) (fun l => f (i.val :: l)) := by
  rw [orderAverage, dite_eq_left hs]

omit [DecidableEq ι] in
theorem orderMass_pos (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (hs : s.Nonempty) : 0 < orderMass w s := by
  exact Finset.sum_pos (fun i hi => hw i hi) hs

theorem orderAverage_nonnegative (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (f : List ι → ℝ) (hf : ∀ l, 0 ≤ f l) :
    0 ≤ orderAverage w s f := by
  induction s using Finset.strongInductionOn generalizing f with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · rw [orderAverage_nonempty w s hs]
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (div_nonneg (hw i i.property).le (orderMass_pos w s hw hs).le)
      exact ih _ (Finset.erase_ssubset i.property)
        (fun j hj => hw j (Finset.mem_of_mem_erase hj)) _ (fun l => hf _)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa only [orderAverage_empty] using hf []

theorem orderAverage_const (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (c : ℝ) : orderAverage w s (fun _ => c) = c := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · rw [orderAverage_nonempty w s hs]
      have hrec (i : s) : orderAverage w (s.erase i.val) (fun _ => c) = c :=
        ih _ (Finset.erase_ssubset i.property)
          (fun j hj => hw j (Finset.mem_of_mem_erase hj))
      simp_rw [hrec]
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have hsum : (∑ i : s, w i) = orderMass w s := Finset.sum_coe_sort s w
      rw [hsum, div_self (orderMass_pos w s hw hs).ne', one_mul]
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact orderAverage_empty _ _

theorem orderAverage_sum {κ : Type*} (w : ι → ℝ) (s : Finset ι)
    (t : Finset κ) (f : κ → List ι → ℝ) :
    orderAverage w s (fun l => ∑ k ∈ t, f k l) =
      ∑ k ∈ t, orderAverage w s (f k) := by
  induction s using Finset.strongInductionOn generalizing f with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · rw [orderAverage_nonempty w s hs]
      have hrec (i : s) :
          orderAverage w (s.erase i.val) (fun l => ∑ k ∈ t, f k (i.val :: l)) =
            ∑ k ∈ t, orderAverage w (s.erase i.val) (fun l => f k (i.val :: l)) :=
        ih _ (Finset.erase_ssubset i.property) _
      simp_rw [hrec]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact (orderAverage_nonempty w s hs (f k)).symm
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simp only [orderAverage_empty]

end LipschitzHilbert

end

end OAI
