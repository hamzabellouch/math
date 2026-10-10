import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests

namespace OAI

/-!
# Fractional height energy from scalar oscillation

A squared cutoff times a centered Lipschitz height is a mean-zero test with an
explicit Lipschitz bound. Scalar Riesz oscillation controls its pairing; combined
with the ball and shell second-moment estimates, this bounds the fractional
pair energy of the rescaled height on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def centeredHeightTestConstant (M c H W : ℝ) (K L : ℝ≥0) : ℝ≥0 :=
  K + 2 * L * Real.toNNReal (W + Real.sqrt (M / c) + (K : ℝ) * H)

theorem lipschitz_height_bound_on_support {d : ℕ}
    (u χ : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (H W b T : ℝ) (hW : |u a| ≤ W) (hb : |b| ≤ T)
    (hsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H) :
    ∀ x, χ x ≠ 0 → |u x - b| ≤ W + T + (K : ℝ) * H := by
  intro x hx
  have hdiff : |u x - u a| ≤ (K : ℝ) * dist x a := by
    simpa only [Real.dist_eq] using! hu.dist_le_mul x a
  have hdist := mul_le_mul_of_nonneg_left (hsupport x hx) K.coe_nonneg
  calc
    |u x - b| ≤ |u x - u a| + |u a - b| := abs_sub_le _ _ _
    _ ≤ (K : ℝ) * H + (|u a| + |b|) :=
      add_le_add (hdiff.trans hdist) (by
        simpa only [sub_zero, zero_sub, abs_neg] using! abs_sub_le (u a) 0 b)
    _ ≤ _ := by linarith

theorem centered_height_test_oscillation_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (u χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hu : LipschitzWith K u) (hχ : LipschitzWith L χ) (hχbound : ∀ x, |χ x| ≤ 1)
    (a : Ambient d) (H R A : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hHA : H < A) (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M c δ W v : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hW : |u a| ≤ W)
    (hcutmass : c ≤ ∫ x in ball a R, χ x ^ 2 ∂μ)
    (hsecond : (∫ x in ball a R, u x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hosc : ScalarOscillationBound (p + 1) μ a A v) :
    |rieszScalarPairing (p + 1) μ a R e
      (fun x => χ x ^ 2 * (u x - cutoffMean (μ.restrict (ball a R)) u χ))| ≤
        ((centeredHeightTestConstant M c H W K L : ℝ) + 1) * v := by
  let ν := μ.restrict (ball a R)
  let b := cutoffMean ν u χ
  let w := fun x => u x - b
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have huL2 := lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a R hR
  have hb : |b| ≤ Real.sqrt (M / c) := cutoffMean_abs_le_uniform ν u χ
    hu.continuous.measurable hχ.continuous.measurable huL2 hχbound c M δ
    hc hM hδ hδ1 hcutmass hsecond
  have hw : LipschitzWith K w := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [w, Real.dist_eq, centered_coordinate_difference] using! hu.dist_le_mul x y
  have hwbound : ∀ x, χ x ≠ 0 → |w x| ≤
      (Real.toNNReal (W + Real.sqrt (M / c) + (K : ℝ) * H) : ℝ) := by
    intro x hx
    exact (lipschitz_height_bound_on_support u χ K hu a H W b (Real.sqrt (M / c))
      hW hb hχsupport x hx).trans (Real.le_coe_toNNReal _)
  have htest := squared_cutoff_height_globally_lipschitz w χ K L
    (Real.toNNReal (W + Real.sqrt (M / c) + (K : ℝ) * H)) hw hχ hχbound hwbound
  have hzeroLocal : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0 :=
    cutoffMean_integral_zero ν u χ hu.continuous.measurable hχ.continuous.measurable
      huL2 hχbound (ne_of_gt (hc.trans_le hcutmass))
  have hzero := squared_cutoff_mean_zero_global μ w χ a H R
    (by linarith) hχsupport hzeroLocal
  have hsupport : ∀ x, χ x ^ 2 * w x ≠ 0 → dist x a ≤ H := by
    intro x hx
    exact hχsupport x (fun hz => hx (by simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]))
  exact oscillation_bound_for_localized_test p C μ hg a A v (hH.trans_lt hHA) hosc e he
    (fun x => χ x ^ 2 * w x) (centeredHeightTestConstant M c H W K L) htest
    H R hH hR hHR hHA hsupport hzero

theorem inner_energy_bound_from_oscillation {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (u χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hu : LipschitzWith K u) (hχ : LipschitzWith L χ)
    (hcoord : ∀ x y, u x - u y = inner ℝ e (x - y))
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (r H R A : ℝ)
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hHR : 2 * H ≤ R) (hrR : r ≤ R) (hHA : H < A)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hχone : ∀ x ∈ ball a r, χ x = 1)
    (M c δ β W : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ1 : 1 ≤ β) (hβ2 : β < 2) (hW : |u a| ≤ W)
    (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hcutmass : c ≤ ∫ x in ball a R, χ x ^ 2 ∂μ)
    (hsecond : (∫ x in ball a R, u x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * β ^ k) ^ 2)
    (hosc : ScalarOscillationBound (p + 1) μ a A (δ ^ 3)) :
    let E := uncenteredEnergyCoefficient p C B M c H R β W
      ((centeredHeightTestConstant M c H W K L : ℝ) + 1) K L
    0 ≤ E ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2)
        ((μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2
          ∂(μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ≤ E := by
  have hsmall := centered_height_test_oscillation_bound p C μ hg e he u χ K L hu hχ hχbound
    a H R A hH (lt_of_lt_of_le zero_lt_one hR) hHR hHA hχsupport
    M c δ W (δ ^ 3) hM hc hδ.le hδ1 hW hcutmass hsecond hosc
  exact uncentered_inner_energy_bound p C B μ hg hCB e u χ K L hu hχ hcoord hχbound
    a r H R hH hR hHR hrR hχsupport hχone M c δ β W
    ((centeredHeightTestConstant M c H W K L : ℝ) + 1) hM hc hδ hδ1 hβ1 hβ2 hW
    (by positivity) N hlast hmass hcutmass hsecond hshell hsmall

end

end RieszRectifiability

end OAI
