import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanCap
import OAI.Analysis.CircleDomains.Uniformization.CyclicCircularization

namespace OAI

/-! After one complete cycle every actual hole has an analytic circle
parametrization. The next one-hole map therefore has the constructed
holomorphic continuation in each source boundary chart. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

lemma cyclic_iterate_analytic {m : ℕ} (C : FiniteJordanConfiguration (Fin (m+1)))
    {n : ℕ} (hn : m+1≤n) (i : Fin (m+1)) :
    IsAnalyticJordanCap ((iterate C (cyclicSchedule m) n).hole i) := by
  apply iterate_analytic_of_visited
  refine ⟨i.val,lt_of_lt_of_le i.isLt hn,?_⟩
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I} {j : I}

omit [Finite I] in
lemma Step.analytic_boundary_continuation (q : Step C j)
    (ha : IsAnalyticJordanCap (C.hole j)) :
    ∃ (α : ℂ → ℂ) (c : ℂ) (r : ℝ), 0<r ∧
      α '' closedBall c r=closure (jordanInterior (C.hole j)) ∧
      ∀p:ℂ,‖p‖=1 → ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
        DifferentiableOn ℂ F V ∧
        EqOn F (fun z => finiteCoord (exteriorDiskNormalization q.center q.radius q.radius_pos
          (q.map (α (roundExteriorBoundaryChart c r p z) : Sphere))))
          (V∩{z : ℂ | 0<z.im}) := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,he⟩ := ha
  refine ⟨α,c,r,hr,he,?_⟩
  intro p hp
  have hf : IsConformalEquivalence q.map
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall q.center q.radius)ᶜ) := by
    simpa only [he,closedTerminalCap] using q.exterior_conformal
  exact analytic_jordan_boundary_continuation hS hα hi hr q.radius_pos hp hDS hf

lemma cyclic_stage_boundary_continuation {m : ℕ}
    (C : FiniteJordanConfiguration (Fin (m+1))) {n : ℕ} (hn : m+1≤n) :
    ∃ (α : ℂ → ℂ) (c : ℂ) (r : ℝ), 0<r ∧
      α '' closedBall c r=closure (jordanInterior ((iterate C (cyclicSchedule m) n).hole
        (cyclicSchedule m n))) ∧
      ∀p:ℂ,‖p‖=1 → ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
        DifferentiableOn ℂ F V ∧
        EqOn F (fun z => finiteCoord (exteriorDiskNormalization
          (selectedCenter C (cyclicSchedule m) n) (selectedRadius C (cyclicSchedule m) n)
          (selectedRadius_pos C (cyclicSchedule m) n)
          (stageMap C (cyclicSchedule m) n (α (roundExteriorBoundaryChart c r p z) : Sphere))))
          (V∩{z : ℂ | 0<z.im}) :=
  (chosenStep (iterate C (cyclicSchedule m) n) (cyclicSchedule m n)).analytic_boundary_continuation
    (cyclic_iterate_analytic C hn _)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
