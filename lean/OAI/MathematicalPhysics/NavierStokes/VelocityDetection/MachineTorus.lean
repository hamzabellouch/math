import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstTotalComparisonClass

namespace OAI

noncomputable section
namespace VelocityDetection.MachineTorus
open Set Function MeasureTheory
open scoped Topology ContDiff BigOperators
open Turing Stacks ChartRouting
variable {b N : ℕ} [NeZero b] [NeZero N]

def data (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) : RoutingData :=
  MachineCylinder.data M w

def initialAddress (w : List (Fin b)) : ℕ :=
  History.address (capacity b (w.length+1) 0) ⟨MachineHistory.initial (N := N) w,0⟩

def force (ν : ℝ) (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) : VectorField 3 :=
  BurstTotal.force (data M w) ν (initialAddress (N := N) w)

def velocity (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : VectorField 3 :=
  BurstTotal.velocity (data M w) ν hν (initialAddress (N := N) w)

def correctnessTrace (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    RoutingArray.Trace (data M w) :=
  HistoryRouting.trace (by omega : 0 < N+1) (NeZero.pos b) (MachineHistory.table M)
    w.length (MachineHistory.initial w) (MachineHistory.initial_fits (NeZero.pos b) w)

@[simp] theorem trace_initial (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    (correctnessTrace M w).address 0 = initialAddress (N := N) w := rfl

theorem trace_active (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    (correctnessTrace M w).stopped 0 = false := by
  change (lookup (NeZero.pos b) (MachineHistory.table M) (MachineHistory.initial w)).isNone = false
  simpa using MachineHistory.initial_active M w

theorem contDiff_force (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : ContDiff ℝ ∞ (uncurry (force ν M w)) :=
  BurstTotal.contDiff_force (data M w) ν hν.le _

theorem force_periodic (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (t : ℝ) : FactorsThrough (force ν M w t) PeriodicSpace.cover :=
  BurstTotal.force_periodic (data M w) ν hν.le _ t

theorem bounded_force (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (T : ℝ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      ‖iteratedFDeriv ℝ d (uncurry (force ν M w)) (t,X)‖ ≤ C :=
  BurstTotal.force_finite_derivative_bounds (data M w) ν hν.le _ T d

theorem force_support (ν : ℝ) (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b))
    (t : ℝ) (X : Coord 3)
    (hX : PeriodicSpace.cover (horizontal X) ∉ PeriodicSpace.cover '' chartSet) :
    force ν M w t X = 0 := by
  let tr := correctnessTrace M w
  exact BurstTotal.force_support (data M w) ν _ (tr.instruction 0 (trace_active M w))
    (tr.source_eq 0 (trace_active M w)) t X hX

theorem contDiff_velocity (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : ContDiff ℝ ∞ (uncurry (velocity ν hν M w)) :=
  BurstTotal.contDiff_velocity (data M w) ν hν _

theorem comparisonClass (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : TorusClass.ComparisonClass (velocity ν hν M w) (fun _ _ => 0) :=
  BurstTotal.comparisonClass (data M w) ν hν _

theorem navierStokes (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : NavierStokes ν (velocity ν hν M w) (fun _ _ => 0) (force ν M w) :=
  BurstTotal.navierStokes (data M w) ν hν _

theorem unique (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {v : VectorField 3} {p : ScalarField 3}
    (hv : TorusClass.ComparisonClass v p) (hNS : NavierStokes ν v p (force ν M w)) :
    ∀ t ≥ 0, (∀ x, v t x = velocity ν hν M w t x) ∧ (∀ x, p t x = 0) :=
  BurstTotal.unique (data M w) ν hν _ hv hNS

theorem detection (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : Observation.torusEvent (velocity ν hν M w) ↔ (TM0.eval M w).Dom :=
  (BurstTotal.detection (data M w) ν (correctnessTrace M w) hν (trace_active M w)).trans
    ((HistoryRouting.trace_stops_iff (by omega : 0 < N+1) (NeZero.pos b) (MachineHistory.table M)
      w.length (MachineHistory.initial w) (MachineHistory.initial_fits (NeZero.pos b) w)).trans
        (MachineHistory.halts_iff M w))

theorem analytic_result (ν : ℝ) (hν : 0 < ν)
    (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    ContDiff ℝ ∞ (uncurry (force ν M w)) ∧
    (∀ t, FactorsThrough (force ν M w t) PeriodicSpace.cover) ∧
    (∃ K : Set (Coord 2), IsCompact K ∧ (∀ X ∈ K, ∀ i, X i ∈ Ioo (0:ℝ) 1) ∧
      ∀ t X, PeriodicSpace.cover (horizontal X) ∉ PeriodicSpace.cover '' K → force ν M w t X = 0) ∧
    (∀ T d, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      ‖iteratedFDeriv ℝ d (uncurry (force ν M w)) (t,X)‖ ≤ C) ∧
    ∃ u : VectorField 3,
      ContDiff ℝ ∞ (uncurry u) ∧ TorusClass.ComparisonClass u (fun _ _ => 0) ∧
      NavierStokes ν u (fun _ _ => 0) (force ν M w) ∧
      (Observation.torusEvent u ↔ (TM0.eval M w).Dom) ∧
      ∀ (v : VectorField 3) (p : ScalarField 3), TorusClass.ComparisonClass v p →
        NavierStokes ν v p (force ν M w) →
        ∀ t ≥ 0, (∀ X, v t X = u t X) ∧ (∀ X, p t X = 0) :=
  ⟨contDiff_force ν hν M w, force_periodic ν hν M w,
    ⟨chartSet,compact_chartSet,fun _ h => chartSet_interior h,force_support ν M w⟩,
    bounded_force ν hν M w, velocity ν hν M w, contDiff_velocity ν hν M w,
    comparisonClass ν hν M w,navierStokes ν hν M w,detection ν hν M w,
    fun _ _ => unique ν hν M w⟩

end VelocityDetection.MachineTorus
end

end OAI
