import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.History
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TapeCodes
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RoutingArray

namespace OAI

noncomputable section
namespace VelocityDetection.HistoryRouting
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Expanding Stacks
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b))

def K (N b m : ℕ) : ℝ := (N * capacity b (m + 1) 0 ^ 2 : ℕ)

def D (N b : ℕ) : ℝ := (b ^ 2 * History.radix N b : ℕ)

theorem K_nonneg (N b m : ℕ) : 0 ≤ K N b m := by unfold K; positivity

include hN hb in

theorem D_ge_one : 1 ≤ D N b := by
  have h := Nat.mul_pos (pow_pos hb 2) (Nat.mul_pos hN hb)
  change (1 : ℝ) ≤ ((b ^ 2 * (N * b) : ℕ) : ℝ)
  exact_mod_cast h

theorem count_eq (m n : ℕ) :
    count (K N b m) (D N b) n =
      ((N * History.radix N b ^ n) * capacity b (m + 1) n ^ 2 : ℕ) := by
  simpa only [count, D, K, Nat.cast_mul, Nat.cast_pow] using
    (congrArg (fun k : ℕ => (k : ℝ)) (History.address_count_geometric (N := N) (b := b) (m + 1) n)).symm

def sign (c : History.Configuration N) : ℝ :=
  if Stacks.lookup hb table c.tape = none then 1 else -1

@[simp] theorem abs_sign (c : History.Configuration N) : |sign hb table c| = 1 := by
  unfold sign
  split_ifs <;> norm_num

def data (m : ℕ) : RoutingData where
  K := K N b m
  D := D N b
  K_nonneg := K_nonneg N b m
  D_ge_one := D_ge_one hN hb
  Instruction n := History.Active hb table (capacity b (m + 1) n) (History.radix N b ^ n)
  finite _ := inferInstance
  source _ := History.sourceAddress hb table
  target _ := History.targetAddress hb table
  sign _ c := sign hb table (History.target hb table c)
  source_injective _ := History.sourceAddress_injective hb table (pow_pos hb _)
  target_injective _ := History.targetAddress_injective hb table (pow_pos hb _)
    (capacity_dvd (by omega))
  source_count n c := by
    rw [count_eq]
    exact_mod_cast History.sourceAddress_count hb table c
  target_count n c := by
    rw [count_eq, capacity_succ, pow_succ']
    exact_mod_cast History.targetAddress_count hb table (capacity_dvd (by omega)) c
  abs_sign _ c := abs_sign hb table (History.target hb table c)

theorem force_bounds (ν : ℝ) (hν : 0 < ν) (m : ℕ) (p : Coord 2) :
    UniformDerivatives.Bounded (fun _ : Unit =>
      uncurry (RoutingArray.force (data hN hb table m) ν p)) :=
  RoutingArray.force_uniformly_bounded (data hN hb table m) ν hν p

end VelocityDetection.HistoryRouting
end

end OAI
