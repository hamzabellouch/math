import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousProfileDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianTransportCalculus

namespace OAI

/-! # Dilation transport preserves the finite-order symbol bounds -/

open scoped ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem halfIdentity_fderiv :
    fderiv ℝ (fun y : E => (1 / 2 : ℝ) • y) =
      fun _ => (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E := by
  funext x
  exact ((hasFDerivAt_id x).const_smul (1 / 2 : ℝ)).fderiv

private theorem halfIdentity_higher_norm (j : ℕ) (hj : 2 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => (1 / 2 : ℝ) • y) x‖ = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + n = (n + 1) + 1 by omega, ← norm_iteratedFDeriv_fderiv,
    halfIdentity_fderiv, iteratedFDeriv_succ_const]
  simp only [Pi.zero_apply, norm_zero]

private theorem halfIdentity_first_norm (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y : E => (1 / 2 : ℝ) • y) x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one, halfIdentity_fderiv, norm_smul]
  norm_num

private theorem halfIdentity_zero_norm (x : E) :
    ‖iteratedFDeriv ℝ 0 (fun y : E => (1 / 2 : ℝ) • y) x‖ ≤ ‖x‖ := by
  rw [norm_iteratedFDeriv_zero, norm_smul]
  norm_num
  linarith [norm_nonneg x]

theorem cartesianTransport_global_symbol (a : ℝ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n (cartesianTransport Q) y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)) := by
  intro n
  obtain ⟨D₀, hD₀, hb₀⟩ := hsymbol n
  obtain ⟨D₁, hD₁, hb₁⟩ := hsymbol (n + 1)
  let D := max D₀ D₁
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
  refine ⟨C * D, mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (hD₀.trans (le_max_left _ _)), ?_⟩
  intro y hy
  have hyr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hprod := norm_iteratedFDeriv_clm_apply (contDiff_infty_iff_fderiv.mp hQ).2
    (contDiff_id.const_smul (1 / 2 : ℝ)) y (by simp : (n : ℕ∞ω) ≤ ∞)
  simp only [id_eq] at hprod
  change ‖iteratedFDeriv ℝ n (cartesianTransport Q) y‖ ≤ _ at hprod
  apply hprod.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (D * ‖y‖ ^ (-2 * a - (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases h0 : n - i = 0
      · have hi_eq : i = n := by omega
        subst i
        rw [Nat.sub_self]
        have hb : ‖iteratedFDeriv ℝ n (fderiv ℝ Q) y‖ ≤ D * ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ)) := by
          rw [norm_iteratedFDeriv_fderiv]
          exact (hb₁ y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        calc
          _ ≤ (n.choose n : ℝ) * (D * ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ))) * ‖y‖ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
              (halfIdentity_zero_norm y) (norm_nonneg _) (by positivity)
          _ = _ := by
            have hp : ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ)) * ‖y‖ = ‖y‖ ^ (-2 * a - (n : ℝ)) := by
              calc
                _ = ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
                _ = ‖y‖ ^ (-2 * a - ((n + 1 : ℕ) : ℝ) + 1) := (Real.rpow_add hyr _ _).symm
                _ = _ := by congr 1; push_cast; ring
            rw [mul_assoc, mul_assoc, hp]
      · by_cases h1 : n - i = 1
        · have hi_eq : i + 1 = n := by omega
          rw [h1]
          have hb : ‖iteratedFDeriv ℝ i (fderiv ℝ Q) y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)) := by
            rw [norm_iteratedFDeriv_fderiv, hi_eq]
            exact (hb₀ y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          calc
            _ ≤ (n.choose i : ℝ) * (D * ‖y‖ ^ (-2 * a - (n : ℝ))) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
                (halfIdentity_first_norm y) (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
        · rw [halfIdentity_higher_norm (n - i) (by omega) y, mul_zero]
          positivity
    _ = C * D * ‖y‖ ^ (-2 * a - (n : ℝ)) := by
      rw [← Finset.sum_mul]
      dsimp only [C]
      ring

end DefocusingNLS

end OAI
