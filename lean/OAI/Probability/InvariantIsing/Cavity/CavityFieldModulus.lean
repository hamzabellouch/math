import OAI.Probability.InvariantIsing.Fields.FieldMagnetizationModulus
import OAI.Probability.InvariantIsing.Cavity.CavityStrictFiniteSpin
import OAI.Probability.InvariantIsing.Cavity.CavityAsymptoticSelfConsistency
import OAI.Probability.InvariantIsing.Cavity.CavityRoundedSelfConsistency

namespace OAI

/-! Uniform plateau control for the actual strict finite cavity fields.
The spectral derivative bound and the conditional-variance estimate
turn convergence of overlap levels into asymptotic preservation of ties. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFieldPrimitive_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (s t : ℝ) :
    |cavityFieldPrimitive rho lam hrho hsum p s -
      cavityFieldPrimitive rho lam hrho hsum p t| ≤ 4 * K^2 * |s - t| := by
  rw [cavityFieldPrimitive_sub]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := 4 * K^2)
    (f := cavityFieldDensity rho lam hrho hsum p) (fun u _ => by
      dsimp only [cavityFieldDensity]
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityRDerivative_nonneg rho lam hrho hsum _)]
      exact cavityRDerivative_le rho lam hrho hsum hK hlam _)
  simpa only [Real.norm_eq_abs] using hb

lemma cavityStrictUniformField_height_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) :
    (cavityStrictUniformField rho lam hrho hsum p n).height i ≤ 4 * K^2 := by
  have hb := cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) (cavityStrictUniformLevels p n i) 0
  have hq := cavityStrictUniformLevels_mem p n i
  have hp0 : cavityFieldPrimitive rho lam hrho hsum (cavityStrictUniformPath p n) 0 = 0 := by
    simp only [cavityFieldPrimitive, intervalIntegral.integral_same]
  rw [hp0, sub_zero, abs_of_nonneg (cavityFieldPrimitive_nonneg _ _ _ _ _ hq.1.le),
    sub_zero, abs_of_pos hq.1] at hb
  exact hb.trans (mul_le_of_le_one_right (by positivity) hq.2.le)

lemma cavityStrictUniformField_magnetization_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (n : ℕ) (i j : Fin (n + 1)) :
    |fieldMagnetizationLevel (cavityStrictUniformField rho lam hrho hsum p n) i -
      fieldMagnetizationLevel (cavityStrictUniformField rho lam hrho hsum p n) j| ≤
      (4 * K^2 * |cavityStrictUniformLevels p n i - cavityStrictUniformLevels p n j|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2)) := by
  have hb := fieldMagnetizationLevel_abs_sub_le
    (cavityStrictUniformField rho lam hrho hsum p n)
    (cavityStrictUniformField_height_le rho lam hrho hsum hK hlam p n (Fin.last n)) i j
  refine hb.trans (mul_le_mul_of_nonneg_right ?_
    (fieldGaussianMomentCap_nonneg (Real.sqrt_nonneg _)))
  exact cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) _ _

theorem cavity_strict_field_asymptotic_ties {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K) (p : OverlapPath) :
    ∃ D : Set ℝ, (∀ᵐ s ∂pathMeasure, s ∈ D) ∧
      ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
        Tendsto (fun n => fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) x -
          fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) y) atTop (𝓝 0) := by
  let D := {s | Tendsto (fun n => cavityStrictUniformPath p n s) atTop (𝓝 (p s)) ∧
    ∀ n, ∃ i : Fin (n + 1), s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)}
  have hD : ∀ᵐ s ∂pathMeasure, s ∈ D := by
    filter_upwards [cavityStrictUniformPath_ae_tendsto p,
      ae_all_iff.mpr (fun n => ae_finite_overlap_cell (uniformCut n)
        (uniformCut_zero n) (uniformCut_last n))] with s hs hc
    exact ⟨hs, hc⟩
  refine ⟨D, hD, ?_⟩
  intro x hx y hy hxy
  have hlim : Tendsto (fun n =>
      (4 * K^2 * |cavityStrictUniformPath p n x - cavityStrictUniformPath p n y|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2))) atTop (𝓝 0) := by
    have hh := ((hx.1.sub hy.1).abs.const_mul (4 * K^2)).mul_const
      (fieldGaussianMomentCap (Real.sqrt (4 * K^2)))
    simpa only [hxy, sub_self, abs_zero, mul_zero, zero_mul] using hh
  apply squeeze_zero_norm (fun n => ?_) hlim
  obtain ⟨i, hi⟩ := hx.2 n
  obtain ⟨j, hj⟩ := hy.2 n
  rw [Real.norm_eq_abs,
    fieldMagnetizationPath_on_cell (cavityStrictUniformField rho lam hrho hsum p n) i hi,
    fieldMagnetizationPath_on_cell (cavityStrictUniformField rho lam hrho hsum p n) j hj,
    cavityStrictUniformPath_on_cell p n i hi, cavityStrictUniformPath_on_cell p n j hj]
  exact cavityStrictUniformField_magnetization_dist_le rho lam hrho hsum hK hlam p n i j

theorem cavity_strict_field_self_consistency {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K) (p : OverlapPath)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun n =>
      ∫ s, Φ (cavityStrictUniformPath p n s) *
        (fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) s -
          cavityStrictUniformPath p n s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s,
      |fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) s - p s|
        ∂pathMeasure) atTop (𝓝 0) := by
  obtain ⟨D, hD, htied⟩ := cavity_strict_field_asymptotic_ties rho lam hrho hsum hK hlam p
  apply cavity_self_consistency_asymptotic_l1_on p
    (fun n => fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n)) D hD htied
  intro Φ
  have hh := (cavity_rounding_test_difference p (cavityStrictUniformPath p)
    (fun n => fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n))
    (cavityStrictUniformPath_ae_tendsto p) Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using hh

end InvariantIsing

end

end OAI
