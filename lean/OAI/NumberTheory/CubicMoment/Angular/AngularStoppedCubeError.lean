import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCubeRoughness
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeError
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.CubeUniformError

namespace OAI

/-! The cube error only needs roughness where the actual coefficient is
nonzero. This avoids imposing roughness on the stopped row's ambient
finite support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_cube_uniform_error (ℓ : ℤ) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (X ξ δ b A u : ℝ),
      1 ≤ X → ξ ≤ 2/5 → 0 < δ → δ ≤ 1 → 2 ≤ b → b ≤ X →
      0 < A → A ≤ 27*(b/2)^2 →
      ∀ (W : ι → ℝ → ℂ) (e : Eisenstein) (j k h : ℕ) (Z Q : ℝ) (early : Bool),
      j ≤ h → 0 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j k h Z Q early)
      ‖cubePoissonContribution S β u Φ A-coprimeCubeMainTerm S β u Φ A‖ ≤
        (C*A/(27*(b/2))+K*A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*
          ((2*Real.log X/Real.log 2)/min (X^ξ) (geometricBinLower (1+δ) X h)))*
          (∑ a ∈ S, ‖β a‖)^2 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cubePoissonContribution_weighted_error Φ hΦ hΦ'
  refine ⟨C,K,hC,hK,?_⟩
  intro X ξ δ b A u hX hξz hδ hδone hb2 hbX hA hAb W e j k h Z Q early hj hR
  dsimp only
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hh := hbound (stoppedIntervalSupport ι X (b/2) b e)
    (fun a ha => ⟨(stoppedIntervalSupport_spec X (b/2) b e ha).1,
      (stoppedIntervalSupport_spec X (b/2) b e ha).2.1⟩) A (b/2)
    ((2*Real.log X/Real.log 2)/min (X^ξ) (geometricBinLower (1+δ) X h))
    hA (by linarith) (by positivity) hAb
    (fun a ha => (Finset.mem_filter.mp ha).2.2.2.1.le)
    (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early)) u
    (fun a ha c hc haz hcz => angular_stopped_pair_prime_reciprocal_log ℓ hX hξz hδ hδone hbX
      W j k h Z Q early hj e ha hc haz hcz hR)
  exact hh.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
