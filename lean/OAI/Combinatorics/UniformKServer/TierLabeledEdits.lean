import Mathlib
import OAI.Combinatorics.UniformKServer.TierLabeledKeys
import OAI.Combinatorics.UniformKServer.TierKeyEdits

namespace OAI

                                       
section

/-! The one-edit noncoverage ledger uses the actual recycled labels. Old
records preserve their labels; the proof does not assume eternal identifiers. -/
noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ} {J : Type*}
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqEdit : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem old_map (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1)
    (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (τ : TierLifetimes.Tape N) (ω : TierKeyEdits.RadiusTape X N K r) (p : X) :
    key r K q c n.val τ ω p=(TierKeyProcess.key r K q c n.val τ ω p).map
      (TierLabels.labels r K q c (n.val+1)).label := by
  unfold key
  cases ho : TierKeyProcess.key r K q c n.val τ ω p with
  | none => rfl
  | some i =>
    have hi := (mem_sort _).mp (TierKeys.key_mem _ _ _ c ω p i ho)
    have hit := TierSchedule.index_lt r K q c n.val i
      ((mem_filter.mp ((TierLifetimes.valid r K hK hq q c n.val).1 τ hi)).1)
    have hin : i≠n := fun he => by have := congrArg Fin.val he; omega
    have hb : TierLabels.birth r K q c n.val=some n := by
      rw [TierLabels.birth,dite_eq_left n.isLt,ite_eq_left hn]
    simp only [Option.map_some]
    congr 1
    exact (@CooldownLabels.label_old (Fin N) (instDecidableEqFin N) (Fintype.card X*K^2) (TierLabels.reserved r K q c) (TierLabels.birth r K q c) n.val n i hb hin).symm

theorem uncovered_map {I L : Type*} (f : I→L) (o : Option I) :
    KeyEdits.uncovered (o.map f)=KeyEdits.uncovered o := by cases o <;> rfl

theorem changed_map {I L : Type*} (e : Option J) (l : L→J) (z : J)
    (f : I→L) (a b : Option I) :
    KeyEdits.changed e l z (a.map f) (b.map f)=KeyEdits.changed e (l∘f) z a b := by
  cases a <;> cases b <;> rfl

theorem stationary (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)+
        KeyEdits.uncovered (key r K q c (n.val+1) τ ω p)-KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      2*(if dist (c n) p≤22*r then 49/(K:ℝ) else 0) := by
  have he (τ : TierLifetimes.Tape N) : KeyEdits.changed (earlier τ) (label τ) (later τ)
      (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)=
      KeyEdits.changed (earlier τ) (label τ∘(TierLabels.labels r K q c (n.val+1)).label) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p) := by
    rw [old_map r K hK hq q c n hn τ ω p]
    exact changed_map _ _ _ _ _ _
  simp_rw [he,key,uncovered_map]
  exact TierKeyEdits.stationary r hr K hK hq q c n hn ω p earlier _ later

theorem mover (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)-
        KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      if dist (c n) p≤22*r then 49/(K:ℝ) else 0 := by
  have he (τ : TierLifetimes.Tape N) : KeyEdits.changed (earlier τ) (label τ) (later τ)
      (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)=
      KeyEdits.changed (earlier τ) (label τ∘(TierLabels.labels r K q c (n.val+1)).label) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p) := by
    rw [old_map r K hK hq q c n hn τ ω p]
    exact changed_map _ _ _ _ _ _
  simp_rw [he,key,uncovered_map]
  exact TierKeyEdits.mover r hr K hK hq q c n hn ω p earlier _ later

end UniformKServer.TierLabeledKeys

end


end

end OAI
