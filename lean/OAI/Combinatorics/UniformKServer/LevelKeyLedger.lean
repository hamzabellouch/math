import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMap
import OAI.Combinatorics.UniformKServer.FirstEdits
import OAI.Combinatorics.UniformKServer.LevelHeavyEdits
import OAI.Combinatorics.UniformKServer.LevelTierLedger
import OAI.Combinatorics.UniformKServer.LevelSerial

namespace OAI

noncomputable section

/-! Full level key edits with the genuine heavy-first serial auxiliary potential. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqKey : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqKey : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqKey : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def keyPotential (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) (ω : Tape D) : ℝ :=
  D.heavyPotential t p+D.tierPotential is t p ω

def heavyStationaryBudget (D : Data X N H) (n : Fin N) (p : X) : ℝ :=
  if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p ∧ dist (D.center n) p≤120*D.r then 2*D.r else 0

def heavyMoverBudget (D : Data X N H) (n : Fin N) (p : X) : ℝ :=
  (if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p then D.r else 0)+
    (if D.heavy n then 0 else dist (D.center n) p)

theorem key_ledger (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p q : X) (a b : ℝ)
    (ha : ∀ ω, D.r*(D.heavyEdit n p ω+D.heavyPotential (n.val+1) q-D.heavyPotential n.val p)≤a)
    (hb : D.r*D.law.expect (fun ω=>D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+
      D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω)≤b) :
    D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)+
      D.keyPotential is (n.val+1) q ω-D.keyPotential is n.val p ω)≤a+b := by
  have he := D.law.expect_mono _ _ ha
  rw [Law.expect_const,Law.expect_mul] at he
  have hbound := mul_le_mul_of_nonneg_left (D.law.expect_mono _ _ (fun ω=>
    add_le_add (D.key_edit_bound n is p ω) (le_refl (D.keyPotential is (n.val+1) q ω-D.keyPotential is n.val p ω)))) D.positive.le
  have hf (ω : Tape D) : D.heavyEdit n p ω+D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+
      (D.keyPotential is (n.val+1) q ω-D.keyPotential is n.val p ω)=
    (D.heavyEdit n p ω+D.heavyPotential (n.val+1) q-D.heavyPotential n.val p)+
    (D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω) := by
    unfold keyPotential; ring
  simp_rw [hf] at hbound
  have hab : D.r*D.law.expect (fun ω=>
      (D.heavyEdit n p ω+D.heavyPotential (n.val+1) q-D.heavyPotential n.val p)+
      (D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω+D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω))≤a+b := by
    rw [Law.expect_add,mul_add]
    exact add_le_add he hb
  simpa only [sub_eq_add_neg,add_assoc] using hbound.trans hab

theorem key_stationary (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)+
      D.keyPotential is (n.val+1) p ω-D.keyPotential is n.val p ω)≤
    D.heavyStationaryBudget n p+(is.map fun i=>D.stationaryBudget γ n i p).sum := by
  exact D.key_ledger n is p p _ _ (D.heavy_stationary n p)
    (D.serial_stationary n is p γ hγ _ (fun hh hp=>D.actual_shadow n p γ hγ hh hp))

theorem key_mover (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)+
      D.keyPotential is (n.val+1) (D.center n) ω-D.keyPotential is n.val p ω)≤
    D.heavyMoverBudget n p+(is.map fun i=>D.moverBudget γ n i p).sum := by
  exact D.key_ledger n is p (D.center n) _ _ (D.heavy_mover n p)
    (D.serial_mover n is p γ _ (fun hh hp=>D.actual_shadow n p γ hγ hh hp))

end UniformKServer.LevelMap.Data

end

end OAI
