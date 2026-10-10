import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyFiniteLaw

namespace OAI

                                
section

/-! Every time slice of the same finite product tape, not a new resampling of
old balls. The slot universe remains independent of the analysis horizon. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords FiniteProbability
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}
local instance tapePairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance tapeFinDecEq (N : ℕ) : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

def slice (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (ω : Fin N → HeavyRadius.Sample (X:=X) r) (t : ℕ) : State X Λ r :=
  run a hr hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr N ω) t

theorem at_radius (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (hN : 0<N) (t : ℕ) (ht : t≤N)
    (ω : Fin N → HeavyRadius.Sample (X:=X) r) (l : Λ) (hl : l∈(slice a hr hΛ h x N ω t).present) :
    (slice a hr hΛ h x N ω t).radius l=HeavyRadius.radius r
      (ω (if hc : births r h x t ((slice a hr hΛ h x N ω t).center l)<N
        then ⟨births r h x t ((slice a hr hΛ h x N ω t).center l),hc⟩ else ⟨0,hN⟩)) := by
  have hb := run_birth a hr hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr N ω) t l hl
  have hn : births r h x t ((slice a hr hΛ h x N ω t).center l)<N := lt_of_lt_of_le hb.1 ht
  have hrad : (slice a hr hΛ h x N ω t).radius l=radiusStream r N ω
      (births r h x t ((slice a hr hΛ h x N ω t).center l)) := hb.2
  rw [hrad]
  simp only [radiusStream,dite_eq_left hn]

theorem at_separation (a : X) (hr : 0 < r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N t : ℕ) (ht : t≤N) (y z : X) :
    (Law.pi (fun _ : Fin N => HeavyRadius.law (X:=X) r)).expect
      (fun ω => if key (slice a hr.le hΛ h x N ω t) y≠key (slice a hr.le hΛ h x N ω t) z then (1:ℝ) else 0)
      ≤ dist y z/r := by
  by_cases hN : 0<N
  · let birth : X → Fin N := fun c => if hc : births r h x t c<N then ⟨births r h x t c,hc⟩ else ⟨0,hN⟩
    exact static_separation hr (HeavySchedule.centers r h x t) (HeavySchedule.centers_separated r h x t)
      birth (fun ω => slice a hr.le hΛ h x N ω t)
      (fun ω => run_centers a hr.le hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr.le N ω) t)
      (fun ω l hl => at_radius a hr.le hΛ h x N hN t ht ω l hl) y z
  · have ht0 : t=0 := by omega
    subst t
    have he (ω : Fin N → HeavyRadius.Sample (X:=X) r) (p : X) :
        key (slice a hr.le hΛ h x N ω 0) p=none := by
      apply (key_none _ p).mpr
      simp only [slice,run,runPair,empty,covers,notMem_empty,false_and,exists_false,not_false_eq_true]
    simp only [he,ne_eq,not_true_eq_false,ite_false,Law.expect_const]
    positivity

end UniformKServer.HeavyProcess

end


end

end OAI
