import OAI.Analysis.CircleDomains.Reflection.AnalyticCircularization

namespace OAI

/-! The actual cyclic boundary continuations are injective, with
nonzero derivative at every point of their open domains. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I} {j : I}

omit [Finite I] in
lemma Step.injective_analytic_boundary_continuation (q : Step C j)
    (ha : IsAnalyticJordanCap (C.hole j)) :
    ∃ (α : ℂ → ℂ) (c : ℂ) (r : ℝ), 0<r ∧
      α '' closedBall c r=closure (jordanInterior (C.hole j)) ∧
      ∀p:ℂ,‖p‖=1 → ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
        DifferentiableOn ℂ F V ∧ InjOn F V ∧
        EqOn F (fun z => finiteCoord (exteriorDiskNormalization q.center q.radius q.radius_pos
          (q.map (α (roundExteriorBoundaryChart c r p z) : Sphere))))
          (V∩{z : ℂ | 0<z.im}) ∧ ∀z∈V,deriv F z≠0 := by
  obtain ⟨S,α,c,r,hS,hr,hDS,hα,hi,he⟩ := ha
  refine ⟨α,c,r,hr,he,?_⟩
  intro p hp
  have hf : IsConformalEquivalence q.map
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall q.center q.radius)ᶜ) := by
    simpa only [he,closedTerminalCap] using q.exterior_conformal
  exact analytic_jordan_boundary_injective_continuation hS hα hi hr q.radius_pos hp hDS hf

lemma cyclic_stage_injective_boundary_continuation {m : ℕ}
    (C : FiniteJordanConfiguration (Fin (m+1))) {n : ℕ} (hn : m+1≤n) :
    ∃ (α : ℂ → ℂ) (c : ℂ) (r : ℝ), 0<r ∧
      α '' closedBall c r=closure (jordanInterior ((iterate C (cyclicSchedule m) n).hole
        (cyclicSchedule m n))) ∧
      ∀p:ℂ,‖p‖=1 → ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
        DifferentiableOn ℂ F V ∧ InjOn F V ∧
        EqOn F (fun z => finiteCoord (exteriorDiskNormalization
          (selectedCenter C (cyclicSchedule m) n) (selectedRadius C (cyclicSchedule m) n)
          (selectedRadius_pos C (cyclicSchedule m) n)
          (stageMap C (cyclicSchedule m) n (α (roundExteriorBoundaryChart c r p z) : Sphere))))
          (V∩{z : ℂ | 0<z.im}) ∧ ∀z∈V,deriv F z≠0 :=
  (chosenStep (iterate C (cyclicSchedule m) n) (cyclicSchedule m n )).injective_analytic_boundary_continuation
    (cyclic_iterate_analytic C hn _)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
