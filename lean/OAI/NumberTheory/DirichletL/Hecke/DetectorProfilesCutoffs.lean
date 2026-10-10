import OAI.NumberTheory.DirichletL.Hecke.DetectorFourierActual

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

abbrev cutoff : SchwartzMap ℝ ℂ := QuadraticInitialBound.sieveCutoff

lemma cutoff_one (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : cutoff x = 1 := by
  simp only [cutoff, QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1, Complex.ofReal_one]

lemma cutoff_zero (x : ℝ) (hx : 2 ≤ x) : cutoff x = 0 := by
  rw [QuadraticInitialBound.sieveCutoff_apply]
  have hh := QuadraticInitialBound.sieveBump.zero_of_le_dist (x := x)
    (show QuadraticInitialBound.sieveBump.rOut ≤ dist x 0 by
      change 2 ≤ dist x 0
      simpa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] using hx)
  rw [hh, Complex.ofReal_zero]

lemma cutoff_norm_le (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
  exact QuadraticInitialBound.sieveBump.le_one

lemma annular_log_bound (x : ℝ) (hx : 0 ≤ x)
    (hactive : DyadicTransfer.annularCutoff cutoff x ≠ 0) : |Real.log x| ≤ Real.log 2 := by
  have hh := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
    (by simpa using hactive)
  norm_num at hh
  have hx0 : 0 < x := by linarith
  have hlo := Real.log_le_log (by norm_num : 0 < (2 : ℝ)⁻¹)
    (show (2 : ℝ)⁻¹ ≤ x by linarith)
  rw [Real.log_inv] at hlo
  exact abs_le.mpr ⟨hlo,Real.log_le_log hx0 hh.2.le⟩

theorem exists_product_log_cutoff :
    ∃ Ω : ℝ → ℂ, HasCompactSupport Ω ∧ ContDiff ℝ ∞ Ω ∧
      tsupport Ω ⊆ Set.Icc (-(2*Real.log 2+1)) (2*Real.log 2+1) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        DyadicTransfer.annularCutoff cutoff x ≠ 0 → DyadicTransfer.annularCutoff cutoff y ≠ 0 →
        Ω (Real.log x+Real.log y) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨Ω,hc,hs,hone,hsupp,hzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (2*Real.log 2) (by positivity)
  refine ⟨Ω,hc,hs,hsupp,?_⟩
  intro x y hx hy hax hay
  apply hone
  have hb1 := annular_log_bound x hx hax
  have hb2 := annular_log_bound y hy hay
  exact (abs_add_le _ _).trans (by linarith)

end
end SevenEighths.HeckeDetectorProfiles

end OAI
