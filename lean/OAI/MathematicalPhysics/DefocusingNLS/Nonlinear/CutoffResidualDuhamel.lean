import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMovingPath
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDecayingDuhamel

namespace OAI

/-! # The actual cutoff residual as a moving-scale forcing history -/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def sampledCutoffResidualHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : ℝ → FourierL2 :=
  fun t => sampledCutoffResidualPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ
    (projIcc 0 T hT t)

theorem continuous_sampledCutoffResidualHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (sampledCutoffResidualHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ) :=
  (sampledCutoffResidualPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ).continuous.comp
    continuous_projIcc

/-- The free response to the actual residual retains the small scale factor,
with a constant independent of the starting radius and the length of the slab. -/
theorem exists_cutoffResidual_Duhamel_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) (m : ℕ) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T) (t : ℝ),
        t ∈ Icc 0 T →
        ‖expandingDuhamel a b k L ha hk hL t
          (sampledCutoffResidualHistory a k L T ha ha1 hk hL hT
            χ hχ hχone hχzero m Q hQ)‖ ≤
          C * L ^ (-2 - a) * Real.exp (-a * t / 2) := by
  obtain ⟨N, hb⟩ := exists_sampledCutoffResidualPath_bound a k ha ha1 hk χ hχ hχone hχzero m
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol
  obtain ⟨C, hC, hbound⟩ := hb Q hQ D hD hsymbol
  refine ⟨C, hC, ?_⟩
  intro L T hL hT t ht
  apply expandingDuhamel_fast_source_norm_le a b k L t (C * L ^ (-2 - a)) ha hk hL ht.1
    (mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hL) _))
  intro τ hτ
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans ht.2⟩
  unfold sampledCutoffResidualHistory
  rw [projIcc_of_mem _ hτT]
  exact hbound L T hL ⟨τ, hτT⟩

end DefocusingNLS

end OAI
