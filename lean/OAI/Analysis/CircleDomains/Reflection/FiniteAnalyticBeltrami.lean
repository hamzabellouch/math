import OAI.Analysis.CircleDomains.Selection.FiniteAnalyticRounding
import OAI.Analysis.CircleDomains.Reflection.CompactDiffeomorphismBeltrami

namespace OAI

/-! The actual smooth comparison with a finite circular domain, together with
the compactly supported strict Beltrami coefficient of its inverse. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer CannonBeltrami

lemma exists_finite_analytic_rounding_coefficient {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) (μ : ℂ → ℂ) (k S : ℝ),
      ContDiff ℝ ∞ (P : ℂ → ℂ) ∧ ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
      (∀i,0<r i) ∧
      (∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i)) ∧
      ContDiff ℝ ∞ μ ∧ 0≤k ∧ k<1 ∧ 0<S ∧
      (∀z,‖μ z‖≤k) ∧ (∀z,S≤‖z‖ → μ z=0) ∧
      ∀z,partialBar P.symm z=μ z*partialZ P.symm z := by
  obtain ⟨P,c,r,R,hR,hPs,hPis,hPf,hr,hP⟩ := exists_finite_analytic_rounding C ha
  have hPif : ∀z,R≤‖z‖ → P.symm z=z := by
    intro z hz
    apply P.injective
    rw [P.apply_symm_apply,hPf z hz]
  obtain ⟨μ,k,S,hμ,hk,hk1,hS,hb,hz,he⟩ := compact_diffeomorphism_beltrami P.symm hPis hPs hPif
  exact ⟨P,c,r,μ,k,S,hPs,hPis,hr,hP,hμ,hk,hk1,hS,hb,hz,he⟩

end CircleDomainRigidity

end

end OAI
