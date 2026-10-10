import OAI.Geometry.RCD.Sobolev.CompactGradientRepresentative
import OAI.Geometry.RCD.Sobolev.CutoffPointwiseGradient
import OAI.Geometry.RCD.Sobolev.PoissonCutoffSource

namespace OAI

/-! # Compact extensions of local constant-Laplacian functions

A good cutoff gives an actual L² Laplacian. Local gradient control and a
bounded representative make the extension compact Lipschitz; on the
plateau both the function and its Laplacian agree with the local data.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_compact_extension {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (A L : ℝ≥0) (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    {p : X} {R C : ℝ} (_hR : 0 < R)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C)
    (hsub : closedBall p (2 * R) ⊆ Ω) :
    ∃ (F : SobolevSpace (hausdorff n X) hX.quadratic)
      (d : Lp ℝ 2 (hausdorff n X)) (v : X → ℝ) (Q : ℝ≥0),
      LipschitzWith Q v ∧ HasCompactSupport v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic F =ᵐ[hausdorff n X] v ∧
      IsWeakLaplacian (hausdorff n X) hX.quadratic F d ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic F =ᵐ[(hausdorff n X).restrict (ball p R)]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic f ∧
      d =ᵐ[(hausdorff n X).restrict (ball p R)] (fun _ => c) := by
  let := hX.separable
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hb (x : X) : |χ.weight x| ≤ (1 : ℝ≥0) := by
    rw [abs_of_nonneg (χ.bounds x).1]
    exact (χ.bounds x).2
  let F := SobolevSpace.cutoffCLM μ hX.quadratic χ.lipschitz
    (χ.hasCompactSupport μ hX.quadratic) hb (fun x => (χ.bounds x).1) f
  have hFrep : SobolevSpace.toLp μ hX.quadratic F =ᵐ[μ]
      fun x => χ.weight x * SobolevSpace.toLp μ hX.quadratic f x :=
    SobolevSpace.cutoffCLM_coe μ hX.quadratic χ.lipschitz
      (χ.hasCompactSupport μ hX.quadratic) hb (fun x => (χ.bounds x).1) f
  obtain ⟨d, hd, hdrep⟩ := hf.cutoff_weakLaplacian μ hX.quadratic f χ.sobolev c χ.laplacian
    χ.weak_laplacian χ.lipschitz (χ.hasCompactSupport μ hX.quadratic) hb
    (fun x => (χ.bounds x).1) ((χ.tsupport_subset μ hX.quadratic).trans hsub) χ.representative hA
  let J : ℝ≥0 := (C / R).toNNReal
  let Q : ℝ≥0 := ⟨Real.sqrt (2 * (L : ℝ) ^ 2 + 2 * (A : ℝ) ^ 2 * (J : ℝ) ^ 2), Real.sqrt_nonneg _⟩
  have hL' := (ae_restrict_iff' hΩ).mp hL
  have hχg := SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic χ.sobolev χ.lipschitz χ.representative
  have hFg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic F x ≤ Q := by
    filter_upwards [minimalSlope_cutoffCLM_sq_le μ hX.quadratic f χ.sobolev χ.lipschitz
      (χ.hasCompactSupport μ hX.quadratic) hb (fun x => (χ.bounds x).1) χ.representative,
      hFrep, χ.representative, hχg, hA, hL', localGamma_self μ hX.quadratic f,
      SobolevSpace.minimalSlope_zero_on_level μ hX.quadratic F 0,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic χ.sobolev)]
      with x hsq hfr hχ hχL hAf hLf hΓ hzero hχ0
    change SobolevSpace.minimalSlope μ hX.quadratic F x ≤ Real.sqrt _
    apply Real.le_sqrt_of_sq_le
    by_cases hx : x ∈ closedBall p (2 * R)
    · have hfG : (SobolevSpace.minimalSlope μ hX.quadratic f x) ^ 2 ≤ (L : ℝ) ^ 2 := by
        rw [← hΓ]
        exact hLf (hsub hx)
      have hfA : (SobolevSpace.toLp μ hX.quadratic f x) ^ 2 ≤ (A : ℝ) ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hAf 2
      have heG : (SobolevSpace.minimalSlope μ hX.quadratic χ.sobolev x) ^ 2 ≤ (J : ℝ) ^ 2 :=
        pow_le_pow_left₀ hχ0 hχL 2
      have hχsq : (SobolevSpace.toLp μ hX.quadratic χ.sobolev x) ^ 2 ≤ 1 := by
        rw [hχ]
        nlinarith [(χ.bounds x).1, (χ.bounds x).2]
      apply hsq.trans
      calc
        _ ≤ 2 * 1 * (L : ℝ) ^ 2 + 2 * (A : ℝ) ^ 2 * (J : ℝ) ^ 2 := by gcongr
        _ = _ := by ring
    · have hχz := χ.zero x (by simpa only [mem_closedBall, not_le, dist_comm] using hx)
      rw [hzero (hfr.trans (by rw [hχz, zero_mul]))]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  have hFzero : ∀ᵐ x ∂μ, 2 * R < dist p x → SobolevSpace.toLp μ hX.quadratic F x = 0 := by
    filter_upwards [hFrep] with x hx hdist
    exact hx.trans (by rw [χ.zero x hdist, zero_mul])
  obtain ⟨v, hv, hvc, _, hvrep⟩ := hX.compact_lipschitz_of_gradient hn F Q hFg p (2 * R) hFzero
  refine ⟨F, d, v, Q, hv, hvc, hvrep, hd, ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [hFrep] with x hx hball
    exact hx.trans (by rw [χ.one x hball, one_mul])
  · apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [hdrep, χ.representative, χ.laplacian_locality,
      localGamma_zero_on_level μ hX.quadratic χ.sobolev f 1,
      localGamma_comm μ hX.quadratic f χ.sobolev] with x hx hχ hΔ hz hcomm hball
    have hχ1 := χ.one x hball
    have hΓ0 : localGamma μ hX.quadratic f χ.sobolev x = 0 := hcomm.trans (hz (hχ.trans hχ1))
    have hdist : dist p x < R := by simpa only [mem_ball, dist_comm] using hball
    rw [hx, hχ1, hΔ (Or.inl hdist), hΓ0]
    ring

end RegularPointCoordinates

end

end OAI
