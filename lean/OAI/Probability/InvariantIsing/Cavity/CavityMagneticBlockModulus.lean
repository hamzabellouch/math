import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockModulus
import OAI.Probability.InvariantIsing.Cavity.CavityFieldModulus

namespace OAI

/-! Asymptotic ties and weak-to-L1 consistency for magnetic block
paths with varying block size and prescribed magnetizations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

lemma cavityStrictUniformField_magneticBlock_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {N : ℕ} (hN : 0 < N) (mag : Fin N → ℝ) (p : OverlapPath) (n : ℕ) (i j : Fin (n + 1)) :
    |magneticBlockLevel (cavityStrictUniformField rho lam hrho hsum p n) mag i -
      magneticBlockLevel (cavityStrictUniformField rho lam hrho hsum p n) mag j| ≤
      (4 * K^2 * |cavityStrictUniformLevels p n i - cavityStrictUniformLevels p n j|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2)) := by
  have hb := magneticBlockLevel_abs_sub_le hN
    (cavityStrictUniformField rho lam hrho hsum p n)
    (cavityStrictUniformField_height_le rho lam hrho hsum hK hlam p n (Fin.last n)) mag i j
  refine hb.trans (mul_le_mul_of_nonneg_right ?_
    (fieldGaussianMomentCap_nonneg (Real.sqrt_nonneg _)))
  exact cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) _ _

theorem cavity_strict_magnetic_block_asymptotic_ties {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (mag : (r : ℕ) → Fin (N r) → ℝ) (p : OverlapPath) :
    ∃ D : Set ℝ, (∀ᵐ s ∂pathMeasure, s ∈ D) ∧
      ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
        Tendsto (fun n => magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n) x -
          magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n) y) atTop (𝓝 0) := by
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
    magneticBlockPath_on_cell (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n) i hi,
    magneticBlockPath_on_cell (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n) j hj,
    cavityStrictUniformPath_on_cell p n i hi, cavityStrictUniformPath_on_cell p n j hj]
  exact cavityStrictUniformField_magneticBlock_dist_le rho lam hrho hsum hK hlam (hN n) (mag n) p n i j

theorem cavity_strict_magnetic_block_self_consistency {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (mag : (r : ℕ) → Fin (N r) → ℝ) (p : OverlapPath)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun n =>
      ∫ s, Φ (cavityStrictUniformPath p n s) *
        (magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n) s -
          cavityStrictUniformPath p n s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s,
      |magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n) s - p s|
        ∂pathMeasure) atTop (𝓝 0) := by
  obtain ⟨D, hD, htied⟩ := cavity_strict_magnetic_block_asymptotic_ties rho lam hrho hsum hK hlam N hN mag p
  apply cavity_self_consistency_asymptotic_l1_on p
    (fun n => magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n)) D hD htied
  intro Φ
  have hh := (cavity_rounding_test_difference p (cavityStrictUniformPath p)
    (fun n => magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum p n) (mag n))
    (cavityStrictUniformPath_ae_tendsto p) Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using hh


end InvariantIsing

end

end OAI
