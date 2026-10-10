import OAI.Probability.InvariantIsing.Cavity.CavityMagneticBlockModulus

namespace OAI

/-! The magnetic overlap argument permits the base quantile and the
finite depth to vary together with the constrained block size. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

theorem cavity_magnetic_diagonal_asymptotic_ties {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (N depth : ℕ → ℕ) (hN : ∀ r, 0 < N r) (mag : (r : ℕ) → Fin (N r) → ℝ)
    (base : ℕ → OverlapPath) (p : OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto
      (fun n => cavityStrictUniformPath (base n) (depth n) s) atTop (𝓝 (p s))) :
    ∃ D : Set ℝ, (∀ᵐ s ∂pathMeasure, s ∈ D) ∧
      ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
        Tendsto (fun n =>
          magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) x -
          magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) y)
          atTop (𝓝 0) := by
  let D := {s | Tendsto (fun n => cavityStrictUniformPath (base n) (depth n) s) atTop (𝓝 (p s)) ∧
    ∀ n, ∃ i : Fin (depth n + 1), s ∈ Ioo (uniformCut (depth n) i.castSucc) (uniformCut (depth n) i.succ)}
  have hD : ∀ᵐ s ∂pathMeasure, s ∈ D := by
    filter_upwards [hq, ae_all_iff.mpr (fun n => ae_finite_overlap_cell
      (uniformCut (depth n)) (uniformCut_zero (depth n)) (uniformCut_last (depth n)))] with s hs hc
    exact ⟨hs, hc⟩
  refine ⟨D, hD, ?_⟩
  intro x hx y hy hxy
  have hlim : Tendsto (fun n =>
      (4 * K^2 * |cavityStrictUniformPath (base n) (depth n) x -
        cavityStrictUniformPath (base n) (depth n) y|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2))) atTop (𝓝 0) := by
    have hh := ((hx.1.sub hy.1).abs.const_mul (4 * K^2)).mul_const
      (fieldGaussianMomentCap (Real.sqrt (4 * K^2)))
    simpa only [hxy, sub_self, abs_zero, mul_zero, zero_mul] using hh
  apply squeeze_zero_norm (fun n => ?_) hlim
  obtain ⟨i, hi⟩ := hx.2 n
  obtain ⟨j, hj⟩ := hy.2 n
  rw [Real.norm_eq_abs,
    magneticBlockPath_on_cell (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) i hi,
    magneticBlockPath_on_cell (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) j hj,
    cavityStrictUniformPath_on_cell (base n) (depth n) i hi,
    cavityStrictUniformPath_on_cell (base n) (depth n) j hj]
  exact cavityStrictUniformField_magneticBlock_dist_le rho lam hrho hsum hK hlam
    (hN n) (mag n) (base n) (depth n) i j

theorem cavity_magnetic_diagonal_self_consistency {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (N depth : ℕ → ℕ) (hN : ∀ r, 0 < N r) (mag : (r : ℕ) → Fin (N r) → ℝ)
    (base : ℕ → OverlapPath) (p : OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto
      (fun n => cavityStrictUniformPath (base n) (depth n) s) atTop (𝓝 (p s)))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun n =>
      ∫ s, Φ (cavityStrictUniformPath (base n) (depth n) s) *
        (magneticBlockPath (hN n)
          (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) s -
          cavityStrictUniformPath (base n) (depth n) s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s,
      |magneticBlockPath (hN n)
        (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) s - p s|
        ∂pathMeasure) atTop (𝓝 0) := by
  obtain ⟨D, hD, htied⟩ := cavity_magnetic_diagonal_asymptotic_ties
    rho lam hrho hsum hK hlam N depth hN mag base p hq
  apply cavity_self_consistency_asymptotic_l1_on p
    (fun n => magneticBlockPath (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n)) D hD htied
  intro Φ
  have hh := (cavity_rounding_test_difference p
    (fun n => cavityStrictUniformPath (base n) (depth n))
    (fun n => magneticBlockPath (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n)) hq Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using hh

end InvariantIsing

end

end OAI
