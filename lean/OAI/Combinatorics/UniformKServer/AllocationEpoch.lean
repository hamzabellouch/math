import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                      
section

/-! Source companion §03, cumulative-variation epochs.  Variation credit is
carried in one potential; a forced parent refresh discards unused credit, and
never creates a fresh initialization allowance. -/
namespace UniformKServer.AllocationEpoch
noncomputable section
open Finset

structure State where
  base : ℝ
  credit : ℝ

def initial (x : ℝ) : State := ⟨x,0⟩

def fires (s : State) (d : ℝ) (parent : Bool) : Prop :=
  parent = true ∨ s.base/100 < s.credit+d

def update (s : State) (x d : ℝ) (parent : Bool) : State := by
  classical
  exact if fires s d parent then initial x else ⟨s.base,s.credit+d⟩

def valid (x : ℝ) (s : State) : Prop :=
  0 ≤ s.base ∧ 0 ≤ s.credit ∧ s.credit ≤ s.base/100 ∧ |x-s.base| ≤ s.credit

def charge (s : State) (x y d : ℝ) (parent : Bool) : ℝ := by
  classical
  exact if fires s d parent then x+y else 0

theorem initial_valid {x : ℝ} (hx : 0 ≤ x) : valid x (initial x) := by
  simp only [valid,initial,sub_self,abs_zero]
  exact ⟨hx,le_rfl,by positivity,le_rfl⟩

theorem update_valid {x y d : ℝ} {s : State} (hs : valid x s)
    (hy : 0 ≤ y) (hd : |y-x| ≤ d) (parent : Bool) :
    valid y (update s y d parent) := by
  have hdn : 0 ≤ d := (abs_nonneg _).trans hd
  unfold update
  split
  · exact initial_valid hy
  · rename_i h
    have hh : s.credit+d ≤ s.base/100 := by
      exact le_of_not_gt (fun h' => h (Or.inr h'))
    refine ⟨hs.1,add_nonneg hs.2.1 hdn,hh,?_⟩
    calc
      |y-s.base| = |(x-s.base)+(y-x)| := by congr 1; ring
      _ ≤ |x-s.base|+|y-x| := abs_add_le _ _
      _ ≤ s.credit+d := add_le_add hs.2.2.2 hd

theorem wholesale_bound {x y d : ℝ} {s : State} (hs : valid x s)
    (hd : |y-x| ≤ d) (hfail : s.base/100 < s.credit+d) :
    x+y ≤ 203*(s.credit+d) := by
  have hx : x ≤ (101/100:ℝ)*s.base := by
    have ha := le_abs_self (x-s.base)
    linarith [hs.2.2.2,hs.2.2.1]
  have hy : y ≤ (101/100:ℝ)*s.base+(s.credit+d) := by
    have ha := le_abs_self (y-x)
    linarith [hs.2.1]
  linarith

theorem credit_step {x y d : ℝ} {s : State} (hs : valid x s)
    (hd : |y-x| ≤ d) (parent : Bool) :
    charge s x y d parent + 203*(update s y d parent).credit ≤
      203*s.credit+203*d+(if parent then x+y else 0) := by
  classical
  by_cases h : fires s d parent
  · simp only [charge,update,ite_eq_left h,initial,mul_zero,add_zero]
    cases parent with
    | false =>
      have hf : s.base/100 < s.credit+d := by simpa [fires] using h
      have hh := wholesale_bound hs hd hf
      simp only [Bool.false_eq_true,↓reduceIte]
      linarith
    | true =>
      simp only [↓reduceIte]
      have hdn : 0 ≤ d := (abs_nonneg _).trans hd
      linarith [hs.2.1]
  · simp only [charge,update,ite_eq_right h,zero_add]
    have hp : parent = false := by
      cases parent <;> simp_all [fires]
    rw [hp]
    simp only [Bool.false_eq_true,↓reduceIte,add_zero]
    ring_nf
    exact le_rfl

def schedule (x d : ℕ → ℝ) (parent : ℕ → Bool) : ℕ → State
  | 0 => initial (x 0)
  | t+1 => update (schedule x d parent t) (x (t+1)) (d t) (parent t)

theorem schedule_valid {x d : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t)
    (hd : ∀ t, |x (t+1)-x t| ≤ d t) (parent : ℕ → Bool) :
    ∀ t, valid (x t) (schedule x d parent t) := by
  intro t
  induction t with
  | zero => exact initial_valid (hx 0)
  | succ t ih => exact update_valid ih (hx (t+1)) (hd t) (parent t)

theorem schedule_budget {x d : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t)
    (hd : ∀ t, |x (t+1)-x t| ≤ d t) (parent : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, charge (schedule x d parent t) (x t) (x (t+1)) (d t) (parent t)) ≤
      203*(∑ t ∈ range H, d t)+
        ∑ t ∈ range H, (if parent t then x t+x (t+1) else 0) := by
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (schedule x d parent t) (x t) (x (t+1)) (d t) (parent t)) +
        203*(schedule x d parent H).credit ≤
      203*(∑ t ∈ range H, d t)+
        ∑ t ∈ range H, (if parent t then x t+x (t+1) else 0) := by
    intro H
    induction H with
    | zero => simp [schedule,initial]
    | succ H ih =>
      rw [sum_range_succ,sum_range_succ,sum_range_succ]
      have ht := credit_step (schedule_valid hx hd parent H) (hd H) (parent H)
      change charge (schedule x d parent H) (x H) (x (H+1)) (d H) (parent H) +
        203*(schedule x d parent (H+1)).credit ≤ _ at ht
      linarith
  have hv := (schedule_valid hx hd parent H).2.1
  linarith [hsum H]

/-- Actual held vectors supply the total-variation hypothesis without degree loss. -/
theorem total_variation {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |(∑ i, b i)-(∑ i, a i)| ≤ ∑ i, |b i-a i| := by
  rw [← sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

end
end UniformKServer.AllocationEpoch

end

end OAI
