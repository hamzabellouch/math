import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyProcess
import OAI.Combinatorics.UniformKServer.HeavySeparation
import OAI.Combinatorics.UniformKServer.HeavyEditPayment

namespace OAI

noncomputable section

/-! End-to-end heavy edits and physical movement, including all no-insertion
cases. The auxiliary potential is the literal [9,10] distance ramp. -/
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords HeavyEditRamp
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem step_stationary_payment (S T : State X Λ r) (hr : 0<r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : Prop) (x : X) (R : ℝ)
    (hR : R∈Set.Icc (16*r) (20*r)) (p : X) :
    editCharge S (step S T hr.le hΛ h x R hR) p+
      r*(parameter r (centers (step S T hr.le hΛ h x R hR)) p-parameter r (centers S) p)≤
      if HeavySchedule.trigger r h (centers S) x ∧ 3*r<dist p x ∧ dist p x≤120*r then 2*r else 0 := by
  by_cases hi : HeavySchedule.trigger r h (centers S) x
  · simp only [step,hi,ite_true,true_and]
    exact stationary_edit_payment S hr x R hR (fresh S T hr.le hΛ) (fresh_absent S T hr.le hΛ).1 p
  · simp only [step,hi,ite_false,false_and,editCharge,ne_eq,not_true_eq_false,ite_false,sub_self,mul_zero,add_zero,le_refl]

theorem step_mover_payment (S T : State X Λ r) (hr : 0<r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : Prop) (x : X) (R : ℝ)
    (hR : R∈Set.Icc (16*r) (20*r)) (y : X) :
    editCharge S (step S T hr.le hΛ h x R hR) y+
      r*(parameter r (centers (step S T hr.le hΛ h x R hR)) x-parameter r (centers S) y)≤
      (if HeavySchedule.trigger r h (centers S) x ∧ 3*r<dist y x then r else 0)+
        (if h then 0 else dist x y) := by
  by_cases hi : HeavySchedule.trigger r h (centers S) x
  · have hh : h := hi.1
    simp only [step,hi,ite_true,true_and,ite_eq_left hh,add_zero]
    exact mover_edit_payment S hr x R hR (fresh S T hr.le hΛ) (fresh_absent S T hr.le hΛ).1 y
  · simp only [step,hi,ite_false,false_and,zero_add,editCharge,ne_eq,not_true_eq_false]
    by_cases hh : h
    · rw [ite_eq_left hh]
      have hc : ∃ c∈centers S, dist x c≤8*r := by
        by_contra hn
        apply hi
        refine ⟨hh,?_⟩
        push Not at hn
        exact hn
      obtain ⟨c,hc,hd⟩ := hc
      rw [center_zero r hr (centers S) x c hc (by linarith)]
      exact mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith [(parameter_bounds r (centers S) y).1])
    · rw [ite_eq_right hh]
      have hp := (le_abs_self (parameter r (centers S) x-parameter r (centers S) y)).trans
        (parameter_lip r hr (centers S) x y)
      have hb := mul_le_mul_of_nonneg_left hp hr.le
      have he : r*(dist x y/r)=dist x y := by field_simp
      simpa only [he] using hb

theorem run_stationary_payment (a : X) (hr : 0<r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : ℕ→Prop) (x : ℕ→X)
    (R : ℕ→ℝ) (hR : ∀ t, R t∈Set.Icc (16*r) (20*r)) (t : ℕ) (p : X) :
    editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) p+
      r*(parameter r (HeavySchedule.centers r h x (t+1)) p-parameter r (HeavySchedule.centers r h x t) p)≤
      if HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) ∧
        3*r<dist p (x t) ∧ dist p (x t)≤120*r then 2*r else 0 := by
  have hp := step_stationary_payment (run a hr.le hΛ h x R hR t)
    (runPair a hr.le hΛ h x R hR t).1 hr hΛ (h t) (x t) (R t) (hR t) p
  change editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) p+
    r*(parameter r (centers (run a hr.le hΛ h x R hR (t+1))) p-
      parameter r (centers (run a hr.le hΛ h x R hR t)) p)≤_ at hp
  simpa only [run_centers] using hp

theorem run_mover_payment (a : X) (hr : 0<r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : ℕ→Prop) (x : ℕ→X)
    (R : ℕ→ℝ) (hR : ∀ t, R t∈Set.Icc (16*r) (20*r)) (t : ℕ) (y : X) :
    editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) y+
      r*(parameter r (HeavySchedule.centers r h x (t+1)) (x t)-parameter r (HeavySchedule.centers r h x t) y)≤
      (if HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) ∧
        3*r<dist y (x t) then r else 0)+(if h t then 0 else dist (x t) y) := by
  have hp := step_mover_payment (run a hr.le hΛ h x R hR t)
    (runPair a hr.le hΛ h x R hR t).1 hr hΛ (h t) (x t) (R t) (hR t) y
  change editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) y+
    r*(parameter r (centers (run a hr.le hΛ h x R hR (t+1))) (x t)-
      parameter r (centers (run a hr.le hΛ h x R hR t)) y)≤_ at hp
  simpa only [run_centers] using hp

end UniformKServer.HeavyProcess

end

end OAI
