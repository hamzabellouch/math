import Mathlib

namespace OAI

noncomputable section

namespace Problem340

def orbitClockLift {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) (n : ℕ) : ℝ :=
  t₀ + ∑ i ∈ Finset.range n, h (f^[i] x)

@[simp] theorem orbitClockLift_zero {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) : orbitClockLift f h x t₀ 0 = t₀ := by
  simp [orbitClockLift]

theorem orbitClockLift_succ {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) (n : ℕ) :
    orbitClockLift f h x t₀ (n + 1) =
      orbitClockLift f h x t₀ n + h (f^[n] x) := by
  simp only [orbitClockLift, Finset.sum_range_succ, add_assoc]

theorem coe_orbitClockLift {X : Type*} (P : ℝ)
    (f : X → X) (h : X → ℝ) (clock : X → AddCircle P)
    (hclock : ∀ x, clock (f x) = clock x + (h x : AddCircle P))
    (x : X) (t₀ : ℝ) (h₀ : (t₀ : AddCircle P) = clock x) (n : ℕ) :
    (orbitClockLift f h x t₀ n : AddCircle P) = clock (f^[n] x) := by
  induction n with
  | zero => simpa using h₀
  | succ n hn =>
      rw [orbitClockLift_succ, Function.iterate_succ_apply', hclock, ← hn]
      simp

theorem monotone_orbitClockLift {X : Type*} (f : X → X) (h : X → ℝ)
    (hh : ∀ x, 0 ≤ h x) (x : X) (t₀ : ℝ) :
    Monotone (orbitClockLift f h x t₀) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [orbitClockLift_succ]
  exact le_add_of_nonneg_right (hh _)

theorem orbitClockLift_step_bounds {X : Type*} (f : X → X) (h : X → ℝ)
    (hh : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1) (x : X) (t₀ : ℝ) (n : ℕ) :
    orbitClockLift f h x t₀ (n + 1) - orbitClockLift f h x t₀ n ∈
      Set.Icc (0 : ℝ) 1 := by
  rw [orbitClockLift_succ, add_sub_cancel_left]
  exact hh _

theorem orbitClockLift_add_initial {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ c : ℝ) (n : ℕ) :
    orbitClockLift f h x (t₀ + c) n = orbitClockLift f h x t₀ n + c := by
  simp only [orbitClockLift]
  ring

theorem orbitClockLift_restart {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) (m n : ℕ) :
    orbitClockLift f h (f^[m] x) (orbitClockLift f h x t₀ m) n =
      orbitClockLift f h x t₀ (m + n) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [orbitClockLift_succ, hn, Nat.add_succ, orbitClockLift_succ]
      congr 1
      rw [← Function.iterate_add_apply, Nat.add_comm n m]

theorem exists_monotone_orbit_clock_lift {X : Type*} (P : ℝ)
    (f : X → X) (h : X → ℝ) (clock : X → AddCircle P)
    (hclock : ∀ x, clock (f x) = clock x + (h x : AddCircle P))
    (hh : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    ∃ t : ℕ → ℝ,
      (∀ n, (t n : AddCircle P) = clock (f^[n] x)) ∧
      (∀ n, t (n + 1) = t n + h (f^[n] x)) ∧
      Monotone t ∧ (∀ n, t (n + 1) - t n ∈ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective (clock x)
  refine ⟨orbitClockLift f h x t₀, ?_, ?_, ?_, ?_⟩
  · exact coe_orbitClockLift P f h clock hclock x t₀ ht₀
  · exact orbitClockLift_succ f h x t₀
  · exact monotone_orbitClockLift f h (fun y => (hh y).1) x t₀
  · exact orbitClockLift_step_bounds f h hh x t₀

end Problem340

end

end OAI
