import Mathlib
import OAI.Combinatorics.UniformKServer.TierSchedule
import OAI.Combinatorics.UniformKServer.TierInsertion

namespace OAI

                                        
section

/-! Deterministic expected short-roster functions on the actual chronological
insertion records. These auxiliary experiments never select actual keys. -/
noncomputable section
namespace UniformKServer.TierShortSchedule
open Finset ShortRoster ChronologicalRoster
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

def run (r : ℝ) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) : ℕ → State (Fin N)
  | 0 => State.empty
  | t+1 => if ht : t<N then
      if TierSchedule.trigger r K (TierSchedule.run r K q c t) q c ⟨t,ht⟩ then
        (run r K s hs q c t).next (TierSchedule.run r K q c t) c r K s hs ⟨t,ht⟩
      else run r K s hs q c t
    else run r K s hs q c t

omit [Fintype X] in
theorem valid (r : ℝ) (K : ℕ) (hK : 0<K) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    (run r K s hs q c t).Valid (TierSchedule.run r K q c t) c r K s := by
  induction t with
  | zero => exact State.empty_valid c r K s
  | succ t ih =>
    by_cases ht : t<N
    · let n : Fin N := ⟨t,ht⟩
      by_cases hn : TierSchedule.trigger r K (TierSchedule.run r K q c t) q c n
      · rw [run,dite_eq_left ht,ite_eq_left hn,TierSchedule.run,dite_eq_left ht,ite_eq_left hn]
        convert (run r K s hs q c t).next_valid _ c r K hK s hs n ih
          (fun i hi => TierSchedule.index_lt r K q c t i hi) using 1
        ext i
        simp only [mem_insert]
        rfl
      · have hn' : ¬TierSchedule.trigger r K (TierSchedule.run r K q c t) q c ⟨t,ht⟩ := hn
        simpa only [run,TierSchedule.run,dite_eq_left ht,ite_eq_right hn'] using ih
    · simpa only [run,TierSchedule.run,dite_eq_right ht] using ih

def parameter (r : ℝ) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) : X → ℝ :=
  (run r K s hs q c t).parameter c r

theorem insertion_payment (P : TierPilot.Parameters) (r h : ℝ) (hr : 0<r) (hh : 1≤h)
    (K : ℕ) (hK : 2≤K) (hlarge : Real.exp (TierInsertion.lifetimeExponent P*h)≤K)
    (hs : 1/Real.sqrt (K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (μ : X → ℝ) (hμ : ∀ p, 0≤μ p)
    (hM : 0<PilotCompact.ballMass r P.gammaH μ (c n))
    (hqual : PilotCompact.ballMass r 20480000 μ (c n)≤
      Real.exp h*PilotCompact.ballMass r P.gammaL μ (c n)) :
    r*TierPilot.insertionMass P r μ (c n)/(K:ℝ)≤
      Real.exp (-h)*(PilotCompact.value r P.sigma 204800 μ
        (parameter r K (1/Real.sqrt (K:ℝ)) hs q c n.val)-
        PilotCompact.value r P.sigma 204800 μ
        (parameter r K (1/Real.sqrt (K:ℝ)) hs q c (n.val+1))) := by
  have htest : ∀ i∈young (TierSchedule.run r K q c n.val) c r K,
      r/2<dist (c n) (c i) := by
    intro i hi
    exact lt_of_not_ge (fun hd => hn.2 ⟨i,hi,hd⟩)
  have hb := TierInsertion.weighted_short_gain P (run r K (1/Real.sqrt (K:ℝ)) hs q c n.val)
    (TierSchedule.run r K q c n.val) c r h hr hh K hK hlarge hs n
    (valid r K (by omega) _ hs q c n.val)
    (fun i hi => TierSchedule.index_lt r K q c n.val i hi) htest μ hμ hM hqual
  simpa only [parameter,run,dite_eq_left n.isLt,ite_eq_left hn] using hb

end UniformKServer.TierShortSchedule

end


end

end OAI
