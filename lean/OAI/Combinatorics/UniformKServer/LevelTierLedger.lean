import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMap
import OAI.Combinatorics.UniformKServer.FirstEdits
import OAI.Combinatorics.UniformKServer.LevelTierEdits

namespace OAI

                                      
section

/-! The complete one-tier end-to-end ledger; movement is included exactly once.
No-insertion qualified tiers contribute zero, not a spurious per-step cost. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqLedger : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqLedger : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqLedger : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def errorIndicator (D : Data X N H) (γ : ℝ) (n : Fin N) (p : X) : ℝ :=
  if dist (D.center n) p≤22*D.r ∧ (¬D.heavy n ∨ γ*D.r<dist (D.center n) p) then 1 else 0

def stationaryBudget (D : Data X N H) (γ : ℝ) (n : Fin N) (i : Fin H) (p : X) : ℝ :=
  if D.tierTrigger n i then 98*D.r/(D.K i:ℝ)*D.errorIndicator γ n p else 0

def moverBudget (D : Data X N H) (γ : ℝ) (n : Fin N) (i : Fin H) (p : X) : ℝ :=
  if D.tierTrigger n i then 49*D.r/(D.K i:ℝ)*D.errorIndicator γ n p
  else if D.qualify i n then 0 else (4+2*Real.log (1+(D.K i:ℝ)^2))*dist (D.center n) p

theorem stationary_ledger (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ) (hγ : γ≤1/2)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
      D.tierUncovered ω (n.val+1) i p-D.tierUncovered ω n.val i p)≤D.stationaryBudget γ n i p := by
  by_cases hn : D.tierTrigger n i
  · have h := mul_le_mul_of_nonneg_left (D.tier_stationary n i p γ hγ hn earlier later he) D.positive.le
    rw [stationaryBudget,ite_eq_left hn]
    exact h.trans_eq (by change D.r*(98/(D.K i:ℝ)*D.errorIndicator γ n p)=_; ring)
  · have hz (ω : Tape D) := D.tierEdit_frozen n i p earlier later hn ω
    have h0 (ω : Tape D) := (hz ω).1
    have h1 (ω : Tape D) := (hz ω).2
    simp only [h0,h1,zero_add,sub_self,Law.expect_const,mul_zero,stationaryBudget,ite_eq_right hn,le_refl]

theorem mover_ledger (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
      D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω n.val i p)≤D.moverBudget γ n i p := by
  by_cases hn : D.tierTrigger n i
  · have hz (ω : Tape D) : D.tierUncovered ω (n.val+1) i (D.center n)=0 :=
      D.tierUncovered_covered n i hn.1 ω
    simp only [hz,add_zero,moverBudget,ite_eq_left hn]
    have h := mul_le_mul_of_nonneg_left (D.tier_mover n i p γ hn earlier later he) D.positive.le
    exact h.trans_eq (by change D.r*(49/(D.K i:ℝ)*D.errorIndicator γ n p)=_; ring)
  · have hz (ω : Tape D) := D.tierEdit_frozen n i p earlier later hn ω
    have h0 (ω : Tape D) := (hz ω).1
    simp only [h0,zero_add,moverBudget,ite_eq_right hn]
    have heq (ω : Tape D) : D.tierUncovered ω n.val i p=D.tierUncovered ω (n.val+1) i p := (hz ω).2.symm
    simp_rw [heq]
    exact D.tierUncovered_motion n i p

end UniformKServer.LevelMap.Data

end


end

end OAI
