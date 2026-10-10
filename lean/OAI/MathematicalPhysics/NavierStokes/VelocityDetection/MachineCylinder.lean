import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MachineHistory
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HistoryRoutingTrace

namespace OAI

noncomputable section
namespace VelocityDetection.MachineCylinder
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
open Set Function MeasureTheory
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def data (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) : RoutingData :=
  HistoryRouting.data (by omega : 0 < N + 1) (NeZero.pos b) (MachineHistory.table M) w.length

def initialPoint (ν : ℝ) (w : List (Fin b)) : Coord 2 :=
  HistoryRouting.initialPoint (N := N + 1) (b := b) w.length (MachineHistory.initial w) ν

def force (ν : ℝ) (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) : VectorField 3 :=
  RoutingArray.force (data M w) ν (initialPoint (N := N) ν w)

def velocity (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : VectorField 3 :=
  RoutingArray.velocity (data M w) ν hν (initialPoint (N := N) ν w)

theorem contDiff_force (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : ContDiff ℝ ∞ (uncurry (force ν M w)) :=
  RoutingArray.contDiff_force (data M w) ν hν _

theorem bounded_force (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) :
    UniformDerivatives.Bounded (fun _ : Unit => uncurry (force ν M w)) :=
  RoutingArray.force_uniformly_bounded (data M w) ν hν _

theorem force_vertical_independent (ν : ℝ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (t : ℝ) (X : Coord 3) (z : ℝ) :
    force ν M w t (update X 2 z) = force ν M w t X :=
  RoutingArray.force_vertical_independent (data M w) ν _ t X z

theorem force_support (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (T : ℝ) :
    ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ∀ X : Coord 3, horizontal X ∉ K → force ν M w t X = 0 := by
  obtain ⟨K, hK, hzero⟩ := RoutingArray.force_finiteCylinderSupport (data M w) ν hν
    (initialPoint (N := N) ν w) T
  exact ⟨K, hK, fun t ht => hzero t ht.1 ht.2⟩

theorem contDiff_velocity (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : ContDiff ℝ ∞ (uncurry (velocity ν hν M w)) :=
  RoutingArray.contDiff_velocity (data M w) ν hν _

theorem comparisonClass (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) :
    Cylinder.ComparisonClass (fun t x => velocity ν hν M w t (Cylinder.join x)) (fun _ _ => 0) :=
  RoutingArray.velocity_comparisonClass (data M w) ν hν _

theorem navierStokes (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : NavierStokes ν (velocity ν hν M w) (fun _ _ => 0) (force ν M w) :=
  RoutingArray.velocity_NavierStokes (data M w) ν hν _

theorem unique (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {v : VectorField 3} {q : ScalarField 3}
    (hv : Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
      (fun t x => q t (Cylinder.join x)))
    (hNS : NavierStokes ν v q (force ν M w)) :
    ∀ t ≥ 0, (∀ x, v t x = velocity ν hν M w t x) ∧ (∀ x, q t x = 0) :=
  RoutingArray.velocity_unique (data M w) ν hν _ hv hNS

theorem vertical_component (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (t : ℝ) (x : Cylinder.Space) :
    velocity ν hν M w t (Cylinder.join x) 2 =
      RoutingArray.scalarSolution (data M w) ν hν (initialPoint (N := N) ν w) t x.1 := by
  change RoutingArray.scalarSolution (data M w) ν hν _ t
    (horizontal (Observation.join x.1 x.2)) = _
  rw [Observation.horizontal_join]

theorem third_component (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (t : ℝ) (ht : 0 ≤ t) :
    (∀ x, 0 ≤ velocity ν hν M w t (Cylinder.join x) 2) ∧
      Integrable (fun x => velocity ν hν M w t (Cylinder.join x) 2) Cylinder.measure := by
  obtain ⟨hpos, hint, _⟩ := RoutingArray.scalarSolution_properties (data M w) ν hν
    (initialPoint (N := N) ν w)
  simp only [vertical_component]
  refine ⟨fun x => hpos t ht x.1, ?_⟩
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by simp only [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact (hint t).comp_fst (volume.restrict (Ioc (0 : ℝ) 1))

theorem detection (ν : ℝ) (hν : 0 < ν) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) :
    Observation.planeEvent (velocity ν hν M w) ↔ (TM0.eval M w).Dom :=
  (HistoryRouting.velocity_detection (by omega : 0 < N + 1) (NeZero.pos b)
    (MachineHistory.table M) w.length (MachineHistory.initial w)
    (MachineHistory.initial_fits (NeZero.pos b) w) ν hν (MachineHistory.initial_active M w)).trans
      (MachineHistory.halts_iff M w)

theorem analytic_result (ν : ℝ) (hν : 0 < ν)
    (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    ContDiff ℝ ∞ (uncurry (force ν M w)) ∧
    UniformDerivatives.Bounded (fun _ : Unit => uncurry (force ν M w)) ∧
    (∀ t X z, force ν M w t (update X 2 z) = force ν M w t X) ∧
    (∀ T : ℝ, ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ∀ X : Coord 3, horizontal X ∉ K → force ν M w t X = 0) ∧
    ∃ u : VectorField 3,
      ContDiff ℝ ∞ (uncurry u) ∧
      Cylinder.ComparisonClass (fun t x => u t (Cylinder.join x)) (fun _ _ => 0) ∧
      NavierStokes ν u (fun _ _ => 0) (force ν M w) ∧
      (∀ t ≥ 0, (∀ x, 0 ≤ u t (Cylinder.join x) 2) ∧
        Integrable (fun x => u t (Cylinder.join x) 2) Cylinder.measure) ∧
      (Observation.planeEvent u ↔ (TM0.eval M w).Dom) ∧
      (∀ (v : VectorField 3) (q : ScalarField 3),
        Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
          (fun t x => q t (Cylinder.join x)) →
        NavierStokes ν v q (force ν M w) →
        ∀ t ≥ 0, (∀ x, v t x = u t x) ∧ (∀ x, q t x = 0)) :=
  ⟨contDiff_force ν hν M w, bounded_force ν hν M w, force_vertical_independent ν M w,
    force_support ν hν M w, velocity ν hν M w, contDiff_velocity ν hν M w,
    comparisonClass ν hν M w, navierStokes ν hν M w, third_component ν hν M w,
    detection ν hν M w, fun _ _ => unique ν hν M w⟩

end VelocityDetection.MachineCylinder
end

end OAI
