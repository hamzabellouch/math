import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymbolMembership
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianDirectionalCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! # Cartesian derivatives of symbol profiles belong to the faithful space -/

open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cartesianDerivative_symbol_decay (a : ℝ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) (v : E) :
    ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n (cartesianDerivative v Q) y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)) := by
  intro n
  obtain ⟨D, hD⟩ := hsymbol (n + 1)
  refine ⟨‖v‖ * max D 0, ?_⟩
  intro y hy
  have hderiv : ‖iteratedFDeriv ℝ n (cartesianDerivative v Q) y‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) Q y‖ := by
    exact (norm_iteratedFDeriv_clm_apply_const
      ((contDiff_infty_iff_fderiv.mp hQ).2.contDiffAt) (by simp)).trans_eq
        (congrArg (‖v‖ * ·) norm_iteratedFDeriv_fderiv)
  have hb : ‖iteratedFDeriv ℝ (n + 1) Q y‖ ≤
      max D 0 * ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ)) :=
    (hD y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hp : ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ)) ≤ ‖y‖ ^ (-2 * a - (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hy (by push_cast; linarith)
  calc
    _ ≤ ‖v‖ * (max D 0 * ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ))) :=
      hderiv.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _ ≤ ‖v‖ * (max D 0 * ‖y‖ ^ (-2 * a - (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (le_max_right _ _)) (norm_nonneg _)
    _ = _ := by ring

theorem homogeneous_profile_directional_derivative (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) (v : E) :
    ∃ q : HomogeneousY a k, ∀ y,
      homogeneousPhysicalCLM a k ha ha1 hk q y = cartesianDerivative v Q y :=
  exists_homogeneous_of_symbol_decay_at_infinity a k ha ha1 hk _
    (cartesianDerivative_contDiff Q hQ v) (cartesianDerivative_symbol_decay a Q hQ hsymbol v)

theorem homogeneous_profile_laplacian (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ q : HomogeneousY a k, ∀ y, homogeneousPhysicalCLM a k ha ha1 hk q y = Δ Q y := by
  classical
  let e := EuclideanSpace.basisFun (Fin 12) ℝ
  have hex (j : Fin 12) := homogeneous_profile_directional_derivative a k ha ha1 hk
    (cartesianDerivative (e j) Q) (cartesianDerivative_contDiff Q hQ (e j))
    (cartesianDerivative_symbol_decay a Q hQ hsymbol (e j)) (e j)
  choose q hq using hex
  refine ⟨∑ j, q j, ?_⟩
  intro y
  rw [map_sum, laplacian_eq_cartesianDerivatives Q hQ]
  change (∑ j, homogeneousPhysicalCLM a k ha ha1 hk (q j) y) = _
  exact Finset.sum_congr rfl (fun j _ => hq j y)

end DefocusingNLS

end OAI
