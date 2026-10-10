import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyEditRamp
import OAI.Combinatorics.UniformKServer.LevelSerial
import OAI.Combinatorics.UniformKServer.LevelKeyLedger

namespace OAI

noncomputable section

/-! Linear auxiliary-potential accounting for a stationary submass and one
unit designated mover. The mover is charged separately from post-request mass. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqMassLedger : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqMassLedger : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMassLedger : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def editCost (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) : ℝ :=
  D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p))

def auxiliary (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) : ℝ :=
  D.r*D.law.expect (D.keyPotential is t p)

def stationaryAllowance (D : Data X N H) (is : List (Fin H)) (γ : ℝ) (n : Fin N) (p : X) : ℝ :=
  D.heavyStationaryBudget n p+(is.map fun i=>D.stationaryBudget γ n i p).sum

def moverAllowance (D : Data X N H) (is : List (Fin H)) (γ : ℝ) (n : Fin N) (p : X) : ℝ :=
  D.heavyMoverBudget n p+(is.map fun i=>D.moverBudget γ n i p).sum

theorem auxiliary_stationary (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.editCost n is p+D.auxiliary is (n.val+1) p-D.auxiliary is n.val p≤D.stationaryAllowance is γ n p := by
  have h := D.key_stationary n is p γ hγ
  rw [Law.expect_sub,Law.expect_add,mul_sub,mul_add] at h
  exact h

theorem auxiliary_mover (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.editCost n is p+D.auxiliary is (n.val+1) (D.center n)-D.auxiliary is n.val p≤D.moverAllowance is γ n p := by
  have h := D.key_mover n is p γ hγ
  rw [Law.expect_sub,Law.expect_add,mul_sub,mul_add] at h
  exact h

theorem mass_ledger (D : Data X N H) (n : Fin N) (is : List (Fin H)) (γ : ℝ) (hγ : γ≤1/2)
    (s ν : X→ℝ) (hs : ∀ p,0≤ s p) (hν : ∀ p,0≤ν p) (hνtotal : ∑ p,ν p=1) :
    (∑ p,(s p+ν p)*D.editCost n is p)+
      ((∑ p,s p*D.auxiliary is (n.val+1) p)+D.auxiliary is (n.val+1) (D.center n))-
      (∑ p,(s p+ν p)*D.auxiliary is n.val p)≤
    (∑ p,s p*D.stationaryAllowance is γ n p)+(∑ p,ν p*D.moverAllowance is γ n p) := by
  have hs' := sum_le_sum (fun p (_ : p∈(univ : Finset X))=>
    mul_le_mul_of_nonneg_left (D.auxiliary_stationary n is p γ hγ) (hs p))
  have hν' := sum_le_sum (fun p (_ : p∈(univ : Finset X))=>
    mul_le_mul_of_nonneg_left (D.auxiliary_mover n is p γ hγ) (hν p))
  have he : (∑ p,s p*(D.editCost n is p+D.auxiliary is (n.val+1) p-D.auxiliary is n.val p))+
      (∑ p,ν p*(D.editCost n is p+D.auxiliary is (n.val+1) (D.center n)-D.auxiliary is n.val p))=
    (∑ p,(s p+ν p)*D.editCost n is p)+
      ((∑ p,s p*D.auxiliary is (n.val+1) p)+D.auxiliary is (n.val+1) (D.center n))-
      (∑ p,(s p+ν p)*D.auxiliary is n.val p) := by
    simp only [mul_sub,mul_add,add_mul,sum_sub_distrib,sum_add_distrib,←sum_mul,hνtotal,one_mul]
    ring
  exact he ▸ add_le_add hs' hν'

theorem auxiliary_bounds (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) :
    0≤D.auxiliary is t p ∧ D.auxiliary is t p≤D.r*(1+is.length) := by
  have hp (ω : Tape D) : 0≤D.keyPotential is t p ω ∧ D.keyPotential is t p ω≤1+is.length := by
    have hh : D.heavyPotential t p∈Set.Icc (0:ℝ) 1 := HeavyEditRamp.parameter_bounds _ _ _
    have ht : 0≤D.tierPotential is t p ω ∧ D.tierPotential is t p ω ≤ is.length := by
      induction is with
      | nil => simp [tierPotential]
      | cons i is ih =>
        have hti : 0≤D.tierUncovered ω t i p ∧ D.tierUncovered ω t i p≤1 := by
          exact KeyEdits.uncovered_bounds _
        simp only [tierPotential,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
        constructor <;> linarith
    unfold keyPotential
    constructor <;> linarith [hh.1,hh.2,ht.1,ht.2]
  constructor
  · exact mul_nonneg D.positive.le (D.law.expect_nonneg _ (fun ω=>(hp ω).1))
  · apply mul_le_mul_of_nonneg_left _ D.positive.le
    calc
      _≤D.law.expect (fun _=>1+(is.length:ℝ)) := D.law.expect_mono _ _ (fun ω=>(hp ω).2)
      _=_ := Law.expect_const _ _

end UniformKServer.LevelMap.Data

end

end OAI
