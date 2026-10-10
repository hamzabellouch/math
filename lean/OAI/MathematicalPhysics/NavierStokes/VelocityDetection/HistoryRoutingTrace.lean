import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RoutingArrayTrace
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HistoryToBox

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
open Set Function
open Stacks
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b))
  (m : ℕ) (c₀ : Stacks.Configuration (Fin N))
  (hc₀ : c₀.leftStack < capacity b (m + 1) 0 ∧ c₀.rightStack < capacity b (m + 1) 0)

def trace : RoutingArray.Trace (data hN hb table m) where
  address n := History.address (capacity b (m + 1) n) (History.orbit hb table ⟨c₀, 0⟩ n)
  stopped n := (lookup hb table (History.orbit hb table ⟨c₀, 0⟩ n).tape).isNone
  instruction n h := History.activeOf hb table _
    (History.orbit_fits hb table (by omega) c₀ hc₀ n) h
  source_eq n h := by
    change History.address _ (History.config (History.activeOf hb table _ _ h).val) = _
    rw [History.config_activeOf]
  target_eq n h := by
    change History.address _ (History.target hb table (History.activeOf hb table _ _ h)) = _
    rw [History.target_activeOf, History.orbit_succ, capacity_succ]
  sign_eq n h := by
    change sign hb table (History.target hb table (History.activeOf hb table _ _ h)) = _
    rw [History.target_activeOf, History.orbit_succ]
    simp only [sign, Option.isNone_iff_eq_none]

theorem trace_stops_iff : (trace hN hb table m c₀ hc₀).Stops ↔ History.Halts hb table c₀ := by
  simp only [RoutingArray.Trace.Stops, trace, Option.isNone_iff_eq_none, History.orbit_tape,
    History.Halts]

def initialPoint (ν : ℝ) : Coord 2 :=
  ![Expanding.spacing ν (K N b m) (D N b) 0 *
      History.address (capacity b (m + 1) 0) ⟨c₀, 0⟩,
    -Expanding.spacing ν (K N b m) (D N b) 0]

include hc₀ in

theorem trace_initialPoint (ν : ℝ) (hactive : (lookup hb table c₀).isSome) :
    RoutingArray.point (data hN hb table m) ν (trace hN hb table m c₀ hc₀) 0 =
      initialPoint (N := N) (b := b) m c₀ ν := by
  have h : (lookup hb table c₀).isNone = false := by simpa using hactive
  simp [RoutingArray.point, RoutingArray.Trace.sign, trace, History.orbit_zero,
    initialPoint, h, data]

include hc₀ in

theorem velocity_detection (ν : ℝ) (hν : 0 < ν) (hactive : (lookup hb table c₀).isSome) :
    Observation.planeEvent (RoutingArray.velocity (data hN hb table m) ν hν
      (initialPoint (N := N) (b := b) m c₀ ν)) ↔ History.Halts hb table c₀ := by
  rw [← trace_initialPoint hN hb table m c₀ hc₀ ν hactive]
  apply (RoutingArray.velocity_detection (data hN hb table m) ν
    (trace hN hb table m c₀ hc₀) hν ?_).trans (trace_stops_iff hN hb table m c₀ hc₀)
  change (lookup hb table c₀).isNone = false
  simpa using hactive

end VelocityDetection.HistoryRouting
end

end OAI
