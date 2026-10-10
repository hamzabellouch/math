import Mathlib
import OAI.Combinatorics.UniformKServer.TierLabels

namespace OAI

                                    
section

/-! Dependence of the chronological insertion/slot schedule only on past true
inputs. No realized lifetime is used to decide a chronological insertion. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type} [MetricSpace X] {N : ℕ}

lemma age_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (i : Fin N)
    (hi : c i=d i) (he : ∀ j∈S, c j=d j) : age S c r i=age S d r i := by
  unfold age
  congr 1
  apply filter_congr
  intro j hj
  rw [hi,he j hj]

lemma young_congr (S : Finset (Fin N)) (c d : Fin N → X) (r : ℝ) (A : ℕ)
    (he : ∀ j∈S, c j=d j) : young S c r A=young S d r A := by
  apply filter_congr
  intro j hj
  rw [age_congr S c d r j (he j hj) he]

lemma trigger_congr (S : Finset (Fin N)) (q v : Fin N → Prop) (c d : Fin N → X)
    (r : ℝ) (K : ℕ) (n : Fin N) (hq : q n ↔ v n) (hc : c n=d n)
    (he : ∀ j∈S, c j=d j) :
    TierSchedule.trigger r K S q c n ↔ TierSchedule.trigger r K S v d n := by
  unfold TierSchedule.trigger
  rw [hq,young_congr S c d r K he,hc]
  apply and_congr_right
  intro _
  apply not_congr
  constructor <;> rintro ⟨i,hi,hd⟩ <;> refine ⟨i,hi,?_⟩
  · rwa [he i (mem_filter.mp hi).1] at hd
  · rwa [he i (mem_filter.mp hi).1]

lemma schedule (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierSchedule.run r K q c t=TierSchedule.run r K v d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))
    simp only [TierSchedule.run]
    by_cases ht : t<N
    · simp only [dite_eq_left ht,hh]
      have he := trigger_congr (TierSchedule.run r K v d t) q v c d r K ⟨t,ht⟩
        (hq ⟨t,ht⟩ (by simp)) (hc ⟨t,ht⟩ (by simp))
        (fun j hj => hc j (Nat.lt_succ_of_lt (TierSchedule.index_lt r K v d t j hj)))
      rw [propext he]
    · simp only [dite_eq_right ht,hh]

lemma reserved (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierLabels.reserved r K q c t=TierLabels.reserved r K v d t := by
  unfold TierLabels.reserved
  rw [schedule r K q v c d t hq hc]
  exact young_congr _ c d r _ (fun j hj => hc j (TierSchedule.index_lt r K v d t j hj))

lemma birth (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val≤t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val≤t → c i=d i) :
    TierLabels.birth r K q c t=TierLabels.birth r K v d t := by
  unfold TierLabels.birth
  by_cases ht : t<N
  · simp only [dite_eq_left ht,schedule r K q v c d t (fun i hi => hq i hi.le) (fun i hi => hc i hi.le)]
    rw [propext (trigger_congr _ q v c d r K ⟨t,ht⟩ (hq _ le_rfl) (hc _ le_rfl)
      (fun j hj => hc j (TierSchedule.index_lt r K v d t j hj).le))]
  · simp only [dite_eq_right ht]

variable [Fintype X]

lemma labels (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierLabels.labels r K q c t=TierLabels.labels r K v d t := by
  unfold TierLabels.labels
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [CooldownLabels.run,CooldownLabels.run,
      reserved r K q v c d t (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega)),
      birth r K q v c d t (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega)),
      ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))]

end UniformKServer.CausalRosters

end


end

end OAI
