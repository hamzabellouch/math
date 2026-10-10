import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PublishedFlowInput
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserInverse

namespace OAI

/-! Finite-dimensional flow regularity for the Moser trajectories. -/

noncomputable section
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem moser_flow_C4 (hpublished : PublishedC4FlowInput) {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
      (∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => flowJacobian G s x)
          (fieldDivergence (moserVelocity rho V t) (G x t) * flowJacobian G t x)
          (Set.Icc (0 : ℝ) 1) t) :=
  hpublished.regularity (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hbound) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) G hG

theorem moser_flow_uniform_derivatives (hpublished : PublishedC4FlowInput) {rho : ℝ}
    (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hc : HasCompactSupport V) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho V) G →
      ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ r (fun y => G y t) x‖ ≤ C := by
  obtain ⟨B, hB⟩ := moserVelocity_four_derivative_bounds hrho V hV hc hbound
  obtain ⟨C, hC, hboundC⟩ := hpublished.uniform B B.coe_nonneg
  exact ⟨C, hC, hboundC (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hbound) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) hB⟩

/-- All properties concern a single family of actual ODE trajectories. -/
theorem moser_C4_bilipschitz_flow_exists (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hc : HasCompactSupport V) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2) :
    ∃ (G : Position → ℝ → Position) (C Cinv : ℝ≥0) (D : ℝ),
      0 < D ∧ IsUnitTimeFlow (moserVelocity rho V) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith C (fun x => G x 1) ∧
      AntilipschitzWith Cinv (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport V → G x 1 = x) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ x,
        ‖iteratedFDeriv ℝ r (fun y => G y 1) x‖ ≤ D) := by
  obtain ⟨G, C, Cinv, hG0, hG, hbij, hC, hCinv, hfix⟩ :=
    moser_bilipschitz_time_one_exists hrho V hV hc hbound
  have hflow : IsUnitTimeFlow (moserVelocity rho V) G := ⟨hG0, hG⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hflow).1
  obtain ⟨D, hD, hderiv⟩ := moser_flow_uniform_derivatives hpublished hrho V hV hc hbound
  have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, le_rfl⟩
  exact ⟨G, C, Cinv, D, hD, hflow, hbij, hC, hCinv, hfix, hreg 1 h1,
    fun r hr hr' x => hderiv G hflow r hr hr' 1 h1 x⟩

end ContinuumCoulomb

end

end OAI
