import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffFamilyContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPotentialContinuity

namespace OAI

/-! # Actual cutoff profiles and residuals along the expanding radius

The sampled profile and its exact PDE residual are continuous histories on
any finite time slab.  The residual decay retains the starting-scale factor.
-/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def sampledCutoffProfilePath (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : C(Icc (0 : ℝ) T, FourierL2) :=
  (⟨fun R : {R : ℝ // 1 ≤ R} => schwartzTorusSample a k R.1 ha1 hk R.2
      (radianFourierKernel (cutoffProfileSchwartz R.1
        (lt_of_lt_of_le zero_lt_one R.2) χ hχ Q hQ)),
    continuous_cutoffProfile_sample a k ha ha1 hk χ hχ Q hQ⟩ :
      C({R : ℝ // 1 ≤ R}, FourierL2)).comp (expandingRadiusCurve L T hL)

noncomputable def sampledCutoffResidualPath (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : C(Icc (0 : ℝ) T, FourierL2) :=
  (⟨fun R : {R : ℝ // 1 ≤ R} => schwartzTorusSample a k R.1 ha1 hk R.2
      (radianFourierKernel (cutoffResidualSchwartz χ hχ hχone hχzero a R.1
        (lt_of_lt_of_le zero_lt_one R.2) m Q hQ)),
    continuous_cutoffResidual_sample a k ha ha1 hk χ hχ hχone hχzero m Q hQ⟩ :
      C({R : ℝ // 1 ≤ R}, FourierL2)).comp (expandingRadiusCurve L T hL)

theorem expandingRadius_residual_power (a L t : ℝ) (hL : 0 < L) :
    (expandingRadius L t) ^ (-2 - a) =
      L ^ (-2 - a) * Real.exp (-(2 + a) * t / 2) := by
  unfold expandingRadius
  rw [Real.mul_rpow hL.le (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  ring

/-- The same constant controls every starting radius and every time slab. -/
theorem exists_sampledCutoffResidualPath_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) (m : ℕ) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (t : Icc (0 : ℝ) T),
        ‖sampledCutoffResidualPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ t‖ ≤
          C * L ^ (-2 - a) * Real.exp (-(2 + a) * (t : ℝ) / 2) := by
  obtain ⟨N, hb⟩ := exists_cutoffResidual_sampling_bound a k ha ha1 hk m χ hχ hχone hχzero
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol
  obtain ⟨C, hC, hbC⟩ := hb Q hQ D hD hsymbol
  refine ⟨C, hC, ?_⟩
  intro L T hL t
  have hR : 1 ≤ expandingRadius L t := hL.trans (expandingRadius_ge L t hL t.2.1)
  have h := hbC (expandingRadius L t) hR
  change ‖sampledCutoffResidualPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ t‖ ≤
    C * (expandingRadius L t) ^ (-2 - a) at h
  rw [expandingRadius_residual_power a L t (lt_of_lt_of_le zero_lt_one hL)] at h
  simpa only [mul_assoc] using h

end DefocusingNLS

end OAI
