import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralGrowthEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExpansionDifferentiation

namespace OAI

/-! # Differentiating arbitrary-order outgoing value expansions

Only the already constructed value expansions and coarse ODE derivative
growth are used. In particular no differentiated asymptotic is assumed.
-/

open Polynomial Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

theorem radialPolynomial_positive_derivative_decay (P : ℂ[X]) (k : ℕ) (hk : 0 < k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv k (radialExteriorPolynomialFunction P) t‖ ≤ B * Real.exp (-2 * t) := by
  have hX : X ∣ P - C (P.coeff 0) := by
    apply X_dvd_iff.mpr
    simp
  obtain ⟨B, hB, hb⟩ := radialExteriorPolynomial_deriv_decay (P - C (P.coeff 0)) 1 k (by simpa using hX)
  refine ⟨B, hB, ?_⟩
  intro t ht
  have he : radialExteriorPolynomialFunction (P - C (P.coeff 0)) =
      radialExteriorPolynomialFunction P - fun _ => P.coeff 0 := by
    funext s
    simp only [radialExteriorPolynomialFunction, eval_sub, eval_C, Pi.sub_apply]
  have h := hb t ht
  rw [he, iteratedDeriv_sub ((radialPolynomialFunction_contDiff P).contDiffAt.of_le (by simp))
    contDiffAt_const, iteratedDeriv_const] at h
  simpa only [Nat.ne_of_gt hk, ite_false, sub_zero, Nat.cast_one, mul_one] using h

theorem radial_arbitrary_approximation_positive_derivative_decay
    (F : ℝ → ℂ) (P : ℕ → ℂ[X]) (L : ℝ)
    (hF : ContDiffOn ℝ ∞ F (Ioi L))
    (hgrowth : ∀ k : ℕ, ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ t, T ≤ t → ‖iteratedDeriv k F t‖ ≤ B * Real.exp (C * t))
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧
      ∀ t, T ≤ t → ‖F t - radialExteriorPolynomialFunction (P j) t‖ ≤
        A * Real.exp (-(2 * (j : ℝ)) * t)) (k : ℕ) (hk : 0 < k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k F t‖ ≤ A * Real.exp (-2 * t) := by
  obtain ⟨j, _hj, A, T, hA, hb⟩ :=
    radial_expansion_derivative_selection F P L hF hgrowth happrox k 2 (by norm_num) 0
  obtain ⟨B, hB, hp⟩ := radialPolynomial_positive_derivative_decay (P j) k hk
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (0 : ℝ),
    eventually_gt_atTop L] with t ht ht0 hLt
  have hf : ContDiffAt ℝ k F t :=
    ((hF t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp)
  have h := hb t ht
  rw [iteratedDeriv_sub hf ((radialPolynomialFunction_contDiff (P j)).contDiffAt.of_le (by simp))] at h
  calc
    ‖iteratedDeriv k F t‖ =
        ‖(iteratedDeriv k F t - iteratedDeriv k (radialExteriorPolynomialFunction (P j)) t) +
          iteratedDeriv k (radialExteriorPolynomialFunction (P j)) t‖ := by rw [sub_add_cancel]
    _ ≤
        ‖iteratedDeriv k F t - iteratedDeriv k (radialExteriorPolynomialFunction (P j)) t‖ +
          ‖iteratedDeriv k (radialExteriorPolynomialFunction (P j)) t‖ :=
      norm_add_le _ _
    _ ≤ A * Real.exp (-2 * t) + B * Real.exp (-2 * t) := add_le_add h (hp t ht0)
    _ = _ := by ring

end DefocusingNLS

end OAI
