import OAI.Geometry.RCD.Sobolev.CurvedCanonicalShiftedHessian
import OAI.Geometry.RCD.Metric.CurvedShiftedDensity
import OAI.Geometry.RCD.Coordinates.CurvedHeatRegularSource
import OAI.Geometry.RCD.Sobolev.ShiftedDensityCutoffBound
import OAI.Geometry.RCD.Heat.HeatBochnerIdentitySource

namespace OAI

/-! # Uniform quantitative Hessian errors from full shifted heat mass

The estimate is simultaneous for every compact Lipschitz direction with
the same gradient bound. The positive shifted density is derived from the
actual scalar dimensional Bochner theorem.
-/

open Set Filter Metric MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_shifted_hessian_eventual_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    (t : ℕ → ℝ) (ht : ∀ k, 0<t k) {R C : ℝ} (hR : 0<R)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (2*R) C)
    (G : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)]
    (v : Y → SobolevSpace (hausdorff n X) hX.quadratic) (V : Y → X → ℝ)
    (Lv : ℝ≥0) (Av : Y → ℝ≥0) (hV : ∀ y, LipschitzWith Lv (V y))
    (hVc : ∀ y, HasCompactSupport (V y))
    (hv : ∀ y, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v y) =ᵐ[hausdorff n X] V y)
    (hAv : ∀ y, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v y) x|≤Av y)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (Dφ : ℝ≥0)
    (hDφ : ∀ᵐ x ∂hausdorff n X, |φ x|≤Dφ)
    (J : ℕ → Y → Lp ℝ 1 ((hausdorff n X).restrict (closedBall p R))) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let w k := heatSobolev μ Q (t k) (ht k) f
    let d k := heatSobolevMap μ Q (t k/2) (half_pos (ht k))
      (-heatGeneratorAt μ Q (t k-t k/2) f)
    (∀ k, SobolevSpace.toLp μ Q (G k) =ᵐ[μ] localGamma μ Q (w k) (w k)) →
    (∀ k (ψ : SobolevSpace μ Q) (z : X → ℝ),
      Continuous z → HasCompactSupport z → tsupport z ⊆ ball p (6*R) →
      SobolevSpace.toLp μ Q ψ =ᵐ[μ] z →
      (∫ x, z x ∂σ k)=-(1/2:ℝ)*energyForm μ Q (G k) ψ-
        weightedGamma μ Q (SobolevSpace.toLp μ Q ψ) (w k) (d k)-
        K*weightedGamma μ Q z (w k) (w k)) →
    (∀ k y, IsCanonicalHeatHessian μ Q (w k) (v y) p R φ (J k y)) →
    ∀ (ell B : ℝ),
      Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
        2*(∫ x, χ.weight x*SobolevSpace.toLp μ Q (d k) x ∂μ)+
        (n:ℝ)*(∫ x, χ.weight x ∂μ)) atTop (𝓝 ell) → ell≤B →
      ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ y (a : ℝ), 0<a →
        4*a*(∫ x in closedBall p R, |J k y x-φ x*localGamma μ Q (v y) (v y) x| ∂μ) ≤
          4*a^2*μ.real (closedBall p R)+((Dφ:ℝ)*((Lv:ℝ)*Real.exp |K|)^2)^2*(B+ε) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  intro μ Q w d hG hσ hJ ell B hlim hB ε hε
  choose W Lw Bd hW hwr hwA hwd hdB using fun k =>
    hX.heat_regular_bounded_source_curved hn hK p f A hA (ht k)
  have hsrc (k : ℕ) : IsMeasureLaplacianOn μ Q (ball p (6*R)) (G k)
      (bochnerGramSource μ Q K (w k) (w k) (d k) (d k) (σ k).toSignedMeasure) :=
    bochner_laplacian_of_energy_identity μ Q K (w k) (d k) (G k) (hG k) (σ k) (hσ k)
  have hpos (k : ℕ) : ∀ᵐ x ∂μ.restrict (closedBall p (2*(2*R))),
      0≤((σ k).rnDeriv μ x).toReal-2*SobolevSpace.toLp μ Q (d k) x+(n:ℝ) :=
    hX.bounded_regular_shifted_density_nonneg hn hK (w k) (d k) (G k) (hwd k)
      (W k) (Lw k) A (Bd k) (hW k) (hwr k) (hwA k) (hdB k) (hG k) p
      (by positivity : 0<6*R) (by linarith : 2*(2*R)<6*R) (σ k) (hsrc k)
  have hmass := χ.shifted_inner_density_eventually_le μ Q σ
    (fun k => SobolevSpace.toLp μ Q (d k)) n hpos measurableSet_closedBall
    (closedBall_subset_ball (by linarith : R<2*R)) hlim hB hε
  filter_upwards [hmass] with k hk y a ha
  have hlocal : IsMeasureLaplacianOn μ Q (ball p (2*R)) (G k)
      (bochnerGramSource μ Q K (w k) (w k) (d k) (d k) (σ k).toSignedMeasure) := by
    intro ψ z hz hzc hzs hψ
    exact hsrc k ψ z hz hzc (hzs.trans (ball_subset_ball (by linarith))) hψ
  have hess := hX.canonical_shifted_hessian_young_curved hn hK (w k) (d k) (G k) (hwd k)
    (W k) (Lw k) A (Bd k) (hW k) (hwr k) (hwA k) (hdB k) (hG k) p hR (σ k) hlocal
    (v y) (V y) Lv (Av y) (hV y) (hVc y) (hv y) (hAv y) φ hφ Dφ hDφ (J k y) (hJ k y) a
  exact hess.trans (add_le_add_right (mul_le_mul_of_nonneg_left hk (sq_nonneg _)) _)

end RegularPointCoordinates

end

end OAI
