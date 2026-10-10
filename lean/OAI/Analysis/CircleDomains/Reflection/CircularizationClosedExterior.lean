import OAI.Analysis.CircleDomains.Reflection.ClosedExteriorBoundaryValues
import OAI.Analysis.CircleDomains.Reflection.AnalyticCircularization

namespace OAI

/-! Each actual cyclic step, after the first cycle, has its canonical
continuous closed-exterior extension and exact circular boundary values. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I} {j : I}

omit [Finite I] in
lemma Step.closed_exterior_extension (q : Step C j)
    (ha : IsAnalyticJordanCap (C.hole j)) :
    let A := (closure (jordanInterior (C.hole j)))ᶜ
    let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization q.center q.radius q.radius_pos
      (q.map (z : Sphere)))
    ContinuousOn (extendFrom A g) (closure A) ∧ EqOn (extendFrom A g) g A :=
  analytic_jordan_closed_exterior_extension ha q.radius_pos q.exterior_conformal

omit [Finite I] in
lemma Step.closed_exterior_boundary_norm (q : Step C j)
    (ha : IsAnalyticJordanCap (C.hole j)) {x : ℂ}
    (hx : x∈frontier (jordanInterior (C.hole j))) :
    ‖extendFrom (closure (jordanInterior (C.hole j)))ᶜ
      (fun z : ℂ => finiteCoord (exteriorDiskNormalization q.center q.radius q.radius_pos
        (q.map (z : Sphere)))) x‖=1 :=
  analytic_jordan_closed_exterior_boundary_norm ha q.radius_pos q.exterior_conformal hx

lemma cyclic_closed_exterior_extension {m : ℕ} (C : FiniteJordanConfiguration (Fin (m+1)))
    {n : ℕ} (hn : m+1≤n) :
    let A := (closure (jordanInterior ((iterate C (cyclicSchedule m) n).hole
      (cyclicSchedule m n))))ᶜ
    let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization
      (selectedCenter C (cyclicSchedule m) n) (selectedRadius C (cyclicSchedule m) n)
      (selectedRadius_pos C (cyclicSchedule m) n) (stageMap C (cyclicSchedule m) n (z : Sphere)))
    ContinuousOn (extendFrom A g) (closure A) ∧ EqOn (extendFrom A g) g A :=
  (chosenStep (iterate C (cyclicSchedule m) n) (cyclicSchedule m n)).closed_exterior_extension
    (cyclic_iterate_analytic C hn _)

lemma cyclic_closed_exterior_boundary_norm {m : ℕ} (C : FiniteJordanConfiguration (Fin (m+1)))
    {n : ℕ} (hn : m+1≤n) {x : ℂ}
    (hx : x∈frontier (jordanInterior ((iterate C (cyclicSchedule m) n).hole (cyclicSchedule m n)))) :
    ‖extendFrom (closure (jordanInterior ((iterate C (cyclicSchedule m) n).hole (cyclicSchedule m n))))ᶜ
      (fun z : ℂ => finiteCoord (exteriorDiskNormalization
        (selectedCenter C (cyclicSchedule m) n) (selectedRadius C (cyclicSchedule m) n)
        (selectedRadius_pos C (cyclicSchedule m) n) (stageMap C (cyclicSchedule m) n (z : Sphere)))) x‖=1 :=
  (chosenStep (iterate C (cyclicSchedule m) n) (cyclicSchedule m n)).closed_exterior_boundary_norm
    (cyclic_iterate_analytic C hn _) hx

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
