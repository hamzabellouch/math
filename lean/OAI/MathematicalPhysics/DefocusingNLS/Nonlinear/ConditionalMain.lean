import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedOpenBlowup
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ClassicalMaximalFlow
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianFullSupport

namespace OAI

/-! # The paper's main statements conditional on the published rectangle Rouché input

The sole explicit published input is `RectangleRouche`, the rectangle specialization
of the corollary after Ahlfors, *Complex Analysis*, third edition, Chapter 4,
§5.2, Theorem 18, p.153. The conclusions combine the profile, spectral, nonlinear, physical-openness
and probabilistic arguments.
-/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

attribute [local irreducible] HasFiniteTimeSelfSimilarBlowup IsClassicalDefocusingFlow
  maximalSobolevInteractionDomain

/-- Theorem 1.1, with an arbitrary lower bound on the odd power. -/
theorem stable_blowup_conditional (hRou : RectangleRouche) (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧ ∀ f ∈ U,
        IsClassicalDefocusingFlow k (by linarith) ((p - 1) / 2) f ∧
        HasFiniteTimeSelfSimilarBlowup k (by linarith) ((p - 1) / 2)
          (1 / ((p : ℝ) - 1)) f := by
  obtain ⟨n, hn, hlarge⟩ := ((radialMatched_exists_open_blowup hRou).and
    (eventually_ge_atTop (max 1 p₀))).exists
  obtain ⟨N, hk, U, hUn, hUo, hU⟩ := hn
  let m := n + radialInnerShootingThreshold
  let p := 2 * m + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hodd : Odd p := ⟨m, rfl⟩
  have hp : p₀ ≤ p := by dsimp [p, m]; omega
  have hp3 : 3 ≤ p := by dsimp [p]; omega
  have hdiv : (p - 1) / 2 = m := by dsimp [p]; omega
  have ha : radialShootingA n = 1 / ((p : ℝ) - 1) := by
    dsimp [radialShootingA, p, m]
    push_cast
    congr 1
    ring
  refine ⟨p, N + 1, hp, hodd, hp3, hk, U, hUn, hUo, ?_⟩
  intro f hf
  refine ⟨maximalSobolev_classical _ _ _ f, ?_⟩
  simpa only [hdiv, ← ha] using hU f hf

/-- Corollary 1.2: the same fixed power and Sobolev order work for every allowed
Gaussian decay exponent. The charged event is an actual open measurable set. -/
theorem gaussian_blowup_conditional (hRou : RectangleRouche) (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧
      (∀ f ∈ U, IsClassicalDefocusingFlow k (by linarith) ((p - 1) / 2) f ∧
        HasFiniteTimeSelfSimilarBlowup k (by linarith) ((p - 1) / 2)
          (1 / ((p : ℝ) - 1)) f) ∧
      ∀ α : ℝ, (k : ℝ) + 6 < α →
        (∀ᵐ g ∂fourierGaussianLaw, Memℓp (weightedGaussianCoefficient k α g) 2) ∧
        (∀ᵐ g ∂fourierGaussianLaw, ∀ n,
          sobolevFourierCoefficient k (weightedGaussianVector k α g) n =
            (1 + ‖n‖ ^ 2) ^ (-α / 2) • g n) ∧
        0 < weightedGaussianLaw k α U := by
  obtain ⟨p, k, hp, hodd, hp3, hk, U, hUn, hUo, hU⟩ := stable_blowup_conditional hRou p₀
  refine ⟨p, k, hp, hodd, hp3, hk, U, hUn, hUo, hU, ?_⟩
  intro α hα
  let : (weightedGaussianLaw k α).IsOpenPosMeasure := weightedGaussianLaw_isOpenPosMeasure k α hα
  exact ⟨ae_mem_l2_gaussian_coefficients k α hα, ae_sobolevFourierCoefficient k α hα,
    hUo.measure_pos _ hUn⟩

end DefocusingNLS

end OAI
