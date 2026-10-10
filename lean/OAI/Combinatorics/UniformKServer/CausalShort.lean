import Mathlib
import OAI.Combinatorics.UniformKServer.CausalRosters
import OAI.Combinatorics.UniformKServer.TierShortSchedule

namespace OAI

                                  
section

/-! The deterministic short-roster pilot is measurable from the true past;
its auxiliary probability space is integrated out, not secretly observed. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset ChronologicalRoster ShortRoster
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

omit [Fintype X] in
lemma short_next (D : State (Fin N)) (S : Finset (Fin N)) (c d : Fin N → X)
    (r : ℝ) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (n : Fin N)
    (hn : c n=d n) (he : ∀ j∈S, c j=d j) (hD : ∀ ω, D.live ω ⊆ S) :
    D.next S c r K s hs n=D.next S d r K s hs n := by
  unfold State.next
  congr 1
  funext ω
  congr 1
  unfold retained
  ext i
  simp only [mem_filter]
  apply and_congr_right
  intro hi
  rw [he i (hD ω.1 hi),hn,age_congr S c d r i (he i (hD ω.1 hi)) he]

omit [Fintype X] in
lemma short_inputs (r : ℝ) (K : ℕ) (hK : 0<K) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierShortSchedule.run r K s hs q c t=TierShortSchedule.run r K s hs v d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))
    simp only [TierShortSchedule.run]
    by_cases ht : t<N
    · simp only [dite_eq_left ht,schedule r K q v c d t (fun i hi => hq i (by omega))
        (fun i hi => hc i (by omega)),hh]
      let S := TierSchedule.run r K v d t
      have he : ∀ j∈S, c j=d j := fun j hj => hc j (Nat.lt_succ_of_lt (TierSchedule.index_lt r K v d t j hj))
      have hn := hc ⟨t,ht⟩ (by simp)
      rw [propext (trigger_congr S q v c d r K ⟨t,ht⟩ (hq _ (by simp)) hn he)]
      split_ifs
      · exact short_next _ S c d r K s hs ⟨t,ht⟩ hn he (fun ω i hi =>
          (mem_filter.mp ((TierShortSchedule.valid r K hK s hs v d t).1 ω hi)).1)
      · rfl
    · simp only [dite_eq_right ht,hh]

omit [Fintype X] in
lemma short_parameter (r : ℝ) (K : ℕ) (hK : 0<K) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierShortSchedule.parameter r K s hs q c t=TierShortSchedule.parameter r K s hs v d t := by
  unfold TierShortSchedule.parameter
  rw [short_inputs r K hK s hs q v c d t hq hc]
  funext p
  unfold State.parameter FiniteProbability.Law.expect
  apply sum_congr rfl
  intro ω _
  congr 1
  have he : ((TierShortSchedule.run r K s hs v d t).live ω).image
      (fun i => ramp (dist p (c i)/r)) =
      ((TierShortSchedule.run r K s hs v d t).live ω).image (fun i => ramp (dist p (d i)/r)) := by
    apply image_congr
    intro i hi
    dsimp only
    rw [hc i (TierSchedule.index_lt r K v d t i
      (mem_filter.mp ((TierShortSchedule.valid r K hK s hs v d t).1 ω hi)).1)]
  dsimp only [costValue]
  simp only [he]

end UniformKServer.CausalRosters

end


end

end OAI
