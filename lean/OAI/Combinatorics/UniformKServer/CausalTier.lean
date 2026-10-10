import Mathlib
import OAI.Combinatorics.UniformKServer.TierLabeledKeys
import OAI.Combinatorics.UniformKServer.CausalRosters

namespace OAI

                                 
section

/-! Causality of the realized live roster and its labeled key, with the entire
independent random tape held fixed. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type} [MetricSpace X] {N : ℕ}
local instance causalIndexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

lemma active_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (K : ℕ)
    (n : Fin N) (hn : c n=d n) (he : ∀ j∈S, c j=d j) :
    ∀ i∈S, ActualRoster.active S c r K n i ↔ ActualRoster.active S d r K n i := by
  intro i hi
  unfold ActualRoster.active
  rw [hn,he i hi,age_congr S c d r i (he i hi) he]

lemma compulsory_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (K : ℕ)
    (he : ∀ j∈S, c j=d j) :
    ∀ i∈S, ActualRoster.compulsory S c r K i ↔ ActualRoster.compulsory S d r K i := by
  intro i hi
  unfold ActualRoster.compulsory
  rw [age_congr S c d r i (he i hi) he]

lemma live_subset (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N) :
    TierLifetimes.live r K q c t τ ⊆ TierSchedule.run r K q c t := by
  induction t with
  | zero => exact subset_rfl
  | succ t ih =>
    simp only [TierLifetimes.live,TierSchedule.run]
    split_ifs with ht hn
    · intro i hi
      simp only [mem_insert] at hi ⊢
      rcases hi with hi|hi
      · exact Or.inl hi
      · exact Or.inr (ih (mem_filter.mp hi).1)
    · exact ih
    · exact ih

lemma live_inputs (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (τ : TierLifetimes.Tape N) :
    TierLifetimes.live r K q c t τ=TierLifetimes.live r K v d t τ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))
    simp only [TierLifetimes.live]
    by_cases ht : t<N
    · simp only [dite_eq_left ht,schedule r K q v c d t (fun i hi => hq i (by omega))
        (fun i hi => hc i (by omega)),hh]
      let S := TierSchedule.run r K v d t
      have he : ∀ j∈S, c j=d j := fun j hj => hc j (Nat.lt_succ_of_lt (TierSchedule.index_lt r K v d t j hj))
      have hn := hc ⟨t,ht⟩ (by simp)
      rw [propext (trigger_congr S q v c d r K ⟨t,ht⟩ (hq _ (by simp)) hn he)]
      split_ifs
      · congr 1
        apply filter_congr
        intro i hi
        have his := live_subset r K v d t τ hi
        rw [active_congr S c d r K ⟨t,ht⟩ hn he i his,
          compulsory_congr S c d r K he i his]
      · rfl
    · simp only [dite_eq_right ht,hh]

lemma key_inputs (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    TierKeyProcess.key r K q c t τ ω p=TierKeyProcess.key r K v d t τ ω p := by
  unfold TierKeyProcess.key TierKeys.key
  rw [live_inputs r K q v c d t hq hc τ]
  apply List.find?_congr
  intro i hi
  rw [hc i (TierSchedule.index_lt r K v d t i
    (live_subset r K v d t τ ((mem_sort _).mp hi)))]

variable [Fintype X]

lemma labeled_inputs (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    TierLabeledKeys.key r K q c t τ ω p=TierLabeledKeys.key r K v d t τ ω p := by
  unfold TierLabeledKeys.key
  rw [key_inputs r K q v c d t hq hc τ ω p,labels r K q v c d t hq hc]

end UniformKServer.CausalRosters

end


end

end OAI
