import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.LimitReflectionlessTest
import OAI.Analysis.RieszRectifiability.Rigidity.ReflectionlessAnnularBounds

namespace OAI

/-!
# Reflectionlessness of limits with vanishing oscillation

The scalar Riesz pairing scales linearly in its direction. This extends the
normalized-direction limit test to arbitrary directions and yields scalar
reflectionlessness when compact-test convergence and vanishing oscillation hold.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem rieszScalarPairing_smul_direction {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R c : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing m μ a R (c • e) φ = c * rieszScalarPairing m μ a R e φ := by
  have hi : rieszInteriorIntegrand m (c • e) φ = fun q => c * rieszInteriorIntegrand m e φ q := by
    funext q
    unfold rieszInteriorIntegrand
    rw [real_inner_smul_left]
    ring
  have hf : rieszFarIntegrand m (c • e) φ a = fun q => c * rieszFarIntegrand m e φ a q := by
    funext q
    unfold rieszFarIntegrand
    rw [real_inner_smul_left]
    ring
  unfold rieszScalarPairing
  dsimp only
  rw [hi, hf, integral_const_mul, integral_const_mul]
  ring

theorem limit_scalarReflectionlessAt_of_oscillation {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)] [SFinite ν]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν)
    (a : Ambient d) (ha : a ∈ ν.support) (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j)) :
    ScalarReflectionlessAt (p + 1) ν a := by
  let := hgν.finite_on_compacts
  intro e φ L H R hφ hH hR hHR hs hmean
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a H)
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  let B : ℝ≥0 := Real.toNNReal ((L : ℝ) * H + |φ a|)
  have hB : ∀ x, |φ x| ≤ (B : ℝ) := by
    intro x
    by_cases hx : φ x = 0
    · rw [hx, abs_zero]
      exact B.coe_nonneg
    have hd : |φ x - φ a| ≤ (L : ℝ) * H := by
      have h := hφ.dist_le_mul x a
      rw [Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hs x hx) L.coe_nonneg)
    have ht := abs_add_le (φ x - φ a) (φ a)
    rw [sub_add_cancel] at ht
    exact (ht.trans (add_le_add hd le_rfl)).trans (Real.le_coe_toNNReal _)
  let η := scaledBallBump a 1
  have hη : LipschitzWith 1 η := by
    simpa only [inv_one, Real.toNNReal_one] using! scaledBallBump_lipschitz a 1 zero_lt_one
  have hcη : HasCompactSupport η := scaledBallBump_hasCompactSupport a 1 zero_lt_one
  have hBη : ∀ x, |η x| ≤ (1 : ℝ≥0) := by
    intro x
    change |scaledBallBump a 1 x| ≤ 1
    rw [abs_of_nonneg (scaledBallBump_bounds a 1 x).1]
    exact (scaledBallBump_bounds a 1 x).2
  have hpos : 0 < ν.real (ball a 1) := by
    apply ENNReal.toReal_pos_iff.mpr
    exact ⟨(ν.mem_support_iff_forall a).mp ha (ball a 1) (ball_mem_nhds a zero_lt_one),
      (hgν.2 a 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩
  have hbump : (∫ x, η x ∂ν) ≠ 0 :=
    (hpos.trans_le (scaledBallBump_integral_lower ν a 1 zero_lt_one)).ne'
  let J := max H 2
  have hJ : 0 ≤ J := hH.trans (le_max_left _ _)
  have hsφ : ∀ x, φ x ≠ 0 → dist x a ≤ J := fun x hx => (hs x hx).trans (le_max_left _ _)
  have hsη : ∀ x, η x ≠ 0 → dist x a ≤ J := by
    intro x hx
    have h := scaledBallBump_support_bound a 1 zero_lt_one x hx
    have hb : dist x a ≤ 2 := by simpa only [mul_one] using! h
    exact hb.trans (le_max_right _ _)
  have hunit : ∀ u : Ambient d, ‖u‖ ≤ 1 → rieszScalarPairing (p + 1) ν a R u φ = 0 := by
    intro u hu
    have hz := limit_rieszScalarPairing_zero_of_oscillation p C D μ ν hg hgν hweak a ha A v hA hv hosc
      u hu φ η L 1 B 1 hφ hη hcomp hcη hB hBη J (2 * J + 1) hJ (by positivity) (by linarith)
      hsφ hsη hmean hbump
    have heq := rieszScalarPairing_localization_independent p D ν hgν u φ L hφ
      a a H J R (2 * J + 1) hH hJ hR (by positivity) hHR (by linarith) hs hsφ hmean
    exact heq.trans hz
  let c := ‖e‖ + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hnorm : ‖c⁻¹ • e‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      _ = ‖e‖ / c := by ring
      _ ≤ 1 := (div_le_one hc).mpr (by dsimp only [c]; linarith)
  have hz := hunit (c⁻¹ • e) hnorm
  have heq := rieszScalarPairing_smul_direction (p + 1) ν a R c (c⁻¹ • e) φ
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hz, mul_zero] at heq
  exact heq

theorem ScalarReflectionlessAt.change_center {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a b : Ambient d) (h : ScalarReflectionlessAt (p + 1) μ a) :
    ScalarReflectionlessAt (p + 1) μ b := by
  intro e φ L H R hφ hH hR hHR hs hmean
  let J := H + dist b a
  have hJ : 0 ≤ J := add_nonneg hH dist_nonneg
  have hsA : ∀ x, φ x ≠ 0 → dist x a ≤ J := by
    intro x hx
    have ht := dist_triangle x b a
    have hb := hs x hx
    dsimp only [J]
    linarith
  have hz := h e φ L J (2 * J + 1) hφ hJ (by positivity) (by linarith) hsA hmean
  have heq := rieszScalarPairing_localization_independent p C μ hg e φ L hφ
    a b J H (2 * J + 1) R hJ hH (by positivity) hR (by linarith) hHR hsA hs hmean
  exact heq.symm.trans hz

end

end RieszRectifiability

end OAI
