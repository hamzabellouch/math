import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyProcess

namespace OAI

                                  
section

/-! Input-determined birth times for current heavy centers. Labels and radii may
be random, but their center's birth coordinate never depends on that randomness. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

def births (r : ℝ) (h : ℕ → Prop) (x : ℕ → X) : ℕ → X → ℕ
  | 0 => fun _ => 0
  | t+1 => if HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t)
    then Function.update (births r h x t) (x t) t else births r h x t

theorem run_birth (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) : ∀ l ∈ (run a hr hΛ h x R hR t).present,
      births r h x t ((run a hr hΛ h x R hR t).center l)<t ∧
      (run a hr hΛ h x R hR t).radius l=R (births r h x t ((run a hr hΛ h x R hR t).center l)) := by
  induction t with
  | zero => simp [run,runPair,empty]
  | succ t ih =>
    intro l hl
    let S := run a hr hΛ h x R hR t
    let T := (runPair a hr hΛ h x R hR t).1
    have hc : centers S=HeavySchedule.centers r h x t := run_centers _ _ _ _ _ _ _ _
    change l ∈ (step S T hr hΛ (h t) (x t) (R t) (hR t)).present at hl
    change births r h x (t+1) ((step S T hr hΛ (h t) (x t) (R t) (hR t)).center l)<t+1 ∧
      (step S T hr hΛ (h t) (x t) (R t) (hR t)).radius l=
        R (births r h x (t+1) ((step S T hr hΛ (h t) (x t) (R t) (hR t)).center l))
    by_cases ht : HeavySchedule.trigger r (h t) (centers S) (x t)
    · have ht' : HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) := hc ▸ ht
      simp only [step,ite_eq_left ht] at hl ⊢
      simp only [births,ite_eq_left ht']
      change l ∈ Insert.insert _ (survivors S (x t)) at hl
      rcases mem_insert.mp hl with he | hs
      · subst l
        simp only [HeavyRecords.insert,Function.update_self]
        exact ⟨Nat.lt_succ_self t,trivial⟩
      · have hn : l ≠ chosen S (x t) (R t) (fresh S T hr hΛ) := by
          intro he
          exact chosen_not_survivor S hr (x t) (R t) (hR t).2 _ (fresh_absent S T hr hΛ).1 (he ▸ hs)
        have hx : S.center l ≠ x t := by
          intro he
          have hd := (mem_filter.mp hs).2
          rw [he,dist_self] at hd
          linarith
        simp only [HeavyRecords.insert,Function.update_of_ne hn,Function.update_of_ne hx]
        have hi := ih l (mem_filter.mp hs).1
        exact ⟨hi.1.trans_le (Nat.le_succ t),hi.2⟩
    · have ht' : ¬HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) := hc ▸ ht
      simp only [step,ite_eq_right ht] at hl ⊢
      simp only [births,ite_eq_right ht']
      have hi := ih l hl
      exact ⟨hi.1.trans_le (Nat.le_succ t),hi.2⟩

end UniformKServer.HeavyProcess

end


end

end OAI
