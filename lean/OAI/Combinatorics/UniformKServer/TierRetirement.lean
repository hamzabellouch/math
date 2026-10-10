import Mathlib
import OAI.Combinatorics.UniformKServer.TierKeyProcess

namespace OAI

                                     
section

noncomputable section
namespace UniformKServer.TierRetirement
open FiniteProbability Finset ChronologicalRoster ShortRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [MetricSpace X] {N : ℕ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

def event (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) : Prop :=
  ∃ i, TierKeyProcess.key r K q c n.val τ ω p=some i ∧
    i∈TierLifetimes.live r K q c n.val τ ∧
    i∉retained (ActualRoster.active (TierSchedule.run r K q c n.val) c r K n)
      (ActualRoster.compulsory (TierSchedule.run r K q c n.val) c r K)
      (TierLifetimes.live r K q c n.val τ) (τ n)

/-- Averaged under the true old survivor distribution. Conditioning on a
realized surviving old record (which would invalidate this bound) is not used. -/
theorem probability_bound (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    (TierLifetimes.law (N:=N) K hq).expect (fun τ => if event r K q c n τ ω p then (1:ℝ) else 0)≤
      if dist (c n) p≤22*r then 49/(K:ℝ) else 0 := by
  let S := TierSchedule.run r K q c n.val
  let D := TierLifetimes.state r K hq q c n.val
  let select := fun τ : TierLifetimes.Tape N => TierKeyProcess.key r K q c n.val τ ω p
  have hb := ActualRoster.first_retirement D S c r hr K hK hq n
    (TierLifetimes.valid r K hK hq q c n.val) p select
    (fun τ i hi => TierKeyProcess.covers r hr K hK q c n.val τ ω p i hi)
  let g := fun H : Finset (Fin N) => fun τ' : Fin N → Bool =>
    if ∃ i, TierKeys.key (Real.log (1+(K:ℝ)^2)) r (H.sort (·≤·)) c ω p=some i ∧ i∈H ∧
      i∉retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) H τ' then (1:ℝ) else 0
  have he : (fun τ => if event r K q c n τ ω p then (1:ℝ) else 0)=
      (fun τ => g (TierLifetimes.live r K q c n.val τ) (τ n)) := by
    funext τ
    dsimp only [event,TierKeyProcess.key,g,S]
    congr 1
  rw [he]
  rw [TierLifetimes.fresh_step r K hq q c n g]
  convert hb using 1
  apply Law.expect_congr
  intro z
  dsimp only [g,D,S,select,TierLifetimes.state,ActualRoster.retires,TierKeyProcess.key]
  congr 1

end UniformKServer.TierRetirement

end


end

end OAI
