import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs
import OAI.Combinatorics.UniformKServer.AllocationSchedule

namespace OAI

                                   
section

/-! Held scalar references with forced epoch resets. The potential is not
 restarted: its nonnegative value is discarded on a wholesale step, while
 the full new installation is charged to that step. -/
noncomputable section
namespace UniformKServer.HeldRelative
open Finset AllocationSchedule

def update (δ b x : ℝ) (reset : Bool) : ℝ :=
  if reset then x else relativeUpdate δ b x

def schedule (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Bool) : ℕ → ℝ
  | 0 => x 0
  | t+1 => update δ (schedule δ x reset t) (x (t+1)) (reset t)

theorem update_nonneg {δ b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (r : Bool) :
    0 ≤ update δ b x r := by
  cases r
  · exact relative_nonneg hb hx
  · exact hx

theorem update_compared {δ b x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (r : Bool) :
    compared δ (update δ b x r) x := by
  cases r
  · exact relative_compared hδ hx
  · change compared δ x x
    constructor <;> nlinarith

theorem schedule_nonneg {δ : ℝ} {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t)
    (reset : ℕ → Bool) : ∀ t, 0 ≤ schedule δ x reset t := by
  intro t
  induction t with
  | zero => exact hx 0
  | succ t ih => exact update_nonneg ih (hx (t+1)) (reset t)

theorem schedule_compared {δ : ℝ} {x : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ t, 0 ≤ x t) (reset : ℕ → Bool) :
    ∀ t, compared δ (schedule δ x reset t) (x t) := by
  intro t
  cases t with
  | zero =>
    change compared δ (x 0) (x 0)
    constructor <;> nlinarith [hx 0]
  | succ t => exact update_compared hδ (hx (t+1)) (reset t)

def expenditure (δ K : ℝ) (x : ℕ → ℝ) (reset : ℕ → Bool) (t : ℕ) : ℝ :=
  if reset t then (1+δ)*(x t+x (t+1)) else K*|x (t+1)-x t|

theorem step {δ K b x y : ℝ} (hδ : 0 < δ) (hK : 1+2/δ ≤ K)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hcmp : compared δ b x) (r : Bool) :
    charge b (update δ b y r)+K*|y-update δ b y r| ≤
      K*|x-b|+(if r then (1+δ)*(x+y) else K*|y-x|) := by
  have hKpos : 0 ≤ K := by
    have := div_pos (by norm_num : (0:ℝ)<2) hδ
    linarith
  cases r
  · exact relative_step hδ hK hb hy
  · simp only [update, ite_true, sub_self, abs_zero, mul_zero, add_zero]
    have hch := charge_le hb hy
    have hp := mul_nonneg hKpos (abs_nonneg (x-b))
    have hdy := mul_nonneg hδ.le hy
    have hdx := mul_nonneg hδ.le hx
    have hc := hcmp.2
    nlinarith

theorem budget {δ K : ℝ} {x : ℕ → ℝ} (hδ : 0 < δ) (hK : 1+2/δ ≤ K)
    (hx : ∀ t, 0 ≤ x t) (reset : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, charge (schedule δ x reset t) (schedule δ x reset (t+1))) ≤
      ∑ t ∈ range H, expenditure δ K x reset t := by
  have hKpos : 0 ≤ K := by
    have := div_pos (by norm_num : (0:ℝ)<2) hδ
    linarith
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (schedule δ x reset t) (schedule δ x reset (t+1)))+
        K*|x H-schedule δ x reset H| ≤
      ∑ t ∈ range H, expenditure δ K x reset t := by
    intro H
    induction H with
    | zero => simp [schedule]
    | succ H ih =>
      rw [sum_range_succ, sum_range_succ]
      have ht := step hδ hK (schedule_nonneg hx reset H) (hx H) (hx (H+1))
        (schedule_compared hδ.le hx reset H) (reset H)
      change charge (schedule δ x reset H) (schedule δ x reset (H+1))+
        K*|x (H+1)-schedule δ x reset (H+1)| ≤
        K*|x H-schedule δ x reset H|+expenditure δ K x reset H at ht
      linarith
  have hp := mul_nonneg hKpos (abs_nonneg (x H-schedule δ x reset H))
  linarith [hsum H]

/-- The source charges true side sizes, rather than the held reference.
 On an unforced refresh those true sizes are controlled by the paid charge. -/
theorem true_charge {δ b x y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y)
    (hcmp : compared δ b x) (hne : b ≠ relativeUpdate δ b y) :
    x+y ≤ (1+δ)*charge b (relativeUpdate δ b y) := by
  have he : relativeUpdate δ b y=y := by
    unfold relativeUpdate at *
    split_ifs at * <;> simp_all
  rw [he, charge, ite_eq_right (he ▸ hne)]
  exact side_charge hδ hy hcmp

end UniformKServer.HeldRelative

end


end

end OAI
