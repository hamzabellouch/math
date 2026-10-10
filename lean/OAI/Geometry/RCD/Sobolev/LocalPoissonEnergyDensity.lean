import OAI.Geometry.RCD.Sobolev.PoissonCompactExtension
import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerTest
import OAI.Geometry.RCD.Sobolev.PoissonLocality
import OAI.Geometry.RCD.Sobolev.PositiveSourceTruncation
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates
import OAI.Geometry.RCD.Sobolev.SupportedEnergyLocality

namespace OAI

/-! # Local Poisson energy densities with the original gradient bound

The compact extension supplies Sobolev regularity and Bochner positivity.
Clipping its energy density keeps the original local gradient bound on the
whole space without changing any interior test pairing.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_energy_density_continuous_tests {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (A L : ℝ≥0) (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    {p : X} {R C : ℝ} (hR : 0 < R)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C)
    (hsub : closedBall p (2 * R) ⊆ Ω) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ≤ (L : ℝ) ^ 2) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f f) ∧
      ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p R →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        (∀ x, 0 ≤ v x) →
        0 ≤ -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G ψ -
          K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) := by
  let := hX.separable
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨F, d, v, Q, hv, hvc, hFv, hd, hF, hdc⟩ :=
    hX.poisson_compact_extension hn hΩ f c hf A L hA hL hR χ hsub
  obtain ⟨G₀, hG₀, _, _⟩ := hX.compact_energy_density hn hv hvc p F hFv d hd
  let G := positiveTruncation μ hX.quadratic G₀ ((L : ℝ) ^ 2) (sq_nonneg _)
  have hG₀r : SobolevSpace.toLp μ hX.quadratic G₀ =ᵐ[μ.restrict (ball p R)]
      localGamma μ hX.quadratic F F := ae_restrict_of_ae hG₀
  have hG₀f : SobolevSpace.toLp μ hX.quadratic G₀ =ᵐ[μ.restrict (ball p R)]
      localGamma μ hX.quadratic f f :=
    hG₀r.trans (localGamma_pair_congr_ae μ hX.quadratic hF hF)
  have hbsub : ball p R ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  have hLf := ae_restrict_of_ae_restrict_of_subset hbsub hL
  have heq : SobolevSpace.toLp μ hX.quadratic G =ᵐ[μ.restrict (ball p R)]
      SobolevSpace.toLp μ hX.quadratic G₀ := by
    filter_upwards [ae_restrict_of_ae (positiveTruncation_coe μ hX.quadratic G₀ (sq_nonneg (L : ℝ))),
      hG₀f, hLf, ae_restrict_of_ae (localGamma_self μ hX.quadratic f)] with x hclip hx hbound hself
    rw [hclip, positiveClip, max_eq_left (by rw [hx, hself]; positivity),
      min_eq_left (by rw [hx]; exact hbound)]
  refine ⟨G, positiveTruncation_bounds μ hX.quadratic G₀ (sq_nonneg (L : ℝ)), heq.trans hG₀f, ?_⟩
  intro ψ w hw hwc hws hψ hw0
  have henergy := energyForm_eq_of_test_support μ hX.quadratic measurableSet_ball heq w hψ hws
  have hpair : inner ℝ (SobolevSpace.toLp μ hX.quadratic ψ) (SobolevSpace.toLp μ hX.quadratic G) =
      inner ℝ (SobolevSpace.toLp μ hX.quadratic ψ) (SobolevSpace.toLp μ hX.quadratic G₀) := by
    rw [L2.inner_def, L2.inner_def]
    have heq' := (ae_restrict_iff' measurableSet_ball).mp heq
    apply integral_congr_ae
    filter_upwards [heq', hψ] with x hx hψx
    change SobolevSpace.toLp μ hX.quadratic ψ x = w x at hψx
    by_cases hmem : x ∈ ball p R
    · simp only [Real.inner_apply, hx hmem]
    · have hwz := image_eq_zero_of_notMem_tsupport (fun hm => hmem (hws hm))
      simp only [Real.inner_apply, hψx, hwz, zero_mul]
  let cw : C_c(X, ℝ) := ⟨⟨w, hw⟩, hwc⟩
  have hh := hX.constant_laplacian_bochner_sobolev_test hn hv hvc p F hFv d hd
    measurableSet_ball c hdc G₀ hG₀ ψ hw.measurable hψ hws
    ‖cw.toBoundedContinuousFunction‖₊
    (fun x => cw.toBoundedContinuousFunction.norm_coe_le_norm x) hw0
  rw [henergy, hpair]
  exact hh

theorem NoncollapsedRCD.local_poisson_energy_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (A L : ℝ≥0) (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict Ω,
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ) ^ 2)
    {p : X} {R C : ℝ} (hR : 0 < R)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C)
    (hsub : closedBall p (2 * R) ⊆ Ω) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic G x ≤ (L : ℝ) ^ 2) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f f) ∧
      ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (B : ℝ≥0),
        LipschitzWith B v → HasCompactSupport v → tsupport v ⊆ ball p R →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        (∀ x, 0 ≤ v x) →
        0 ≤ -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G ψ -
          K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) := by
  obtain ⟨G, hGb, hGr, hpos⟩ := hX.local_poisson_energy_density_continuous_tests hn hΩ f c hf A L hA hL hR χ hsub
  exact ⟨G, hGb, hGr, fun ψ v B hv hvc hvs hψ hv0 => hpos ψ v hv.continuous hvc hvs hψ hv0⟩

end RegularPointCoordinates

end

end OAI
