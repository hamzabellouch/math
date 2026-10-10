import OAI.Analysis.CircleDomains.Selection.FixedCircuitExclusion

namespace OAI

/-! Equality of smooth circle coordinates along the whole parametrized
circuit is enough to identify their original form integrals. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_of_eq_on_curve
    {O P : Set ℂ} (hO : IsOpen O) (hP : IsOpen P)
    {u v : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O) (hv : SmoothCircleOn v P)
    (φ : ℂ → ℝ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγO : ∀ t, γ t ∈ O) (hγP : ∀ t, γ t ∈ P)
    (heq : ∀ t, u (γ t) = v (γ t)) :
    circleFormIntegral φ u γ = circleFormIntegral φ v γ := by
  obtain ⟨w, hw, hproj⟩ := exists_smooth_real_circuit_lift hO hu hγ hγO
  rw [circleFormIntegral_eq_real_lift hO hu φ γ (hγ.differentiable (by simp))
    hγO w hw.continuous hproj,
    circleFormIntegral_eq_real_lift hP hv φ γ (hγ.differentiable (by simp))
    hγP w hw.continuous (fun t => (hproj t).trans (heq t))]

end CircleDomainRigidity

end

end OAI
