import OAI.Geometry.RCD.Sobolev.BochnerCutoffFlux
import OAI.Geometry.RCD.Sobolev.WeightedGammaJointLimit

namespace OAI

/-! # Stability of the full Bochner cutoff pairing under strong source limits -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.source_square_tendsto
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    {d : Lp ℝ 2 μ} {ds : ℕ → Lp ℝ 2 μ} (hd : Tendsto ds atTop (𝓝 d)) :
    Tendsto (fun k => ∫ x, χ.weight x*(ds k x)^2 ∂μ) atTop
      (𝓝 (∫ x, χ.weight x*(d x)^2 ∂μ)) := by
  let V := boundedMultiplier μ χ.weight χ.weight.continuous.measurable 1 (fun x => by
    rw [abs_of_nonneg (χ.bounds x).1]; exact (χ.bounds x).2)
  have he (a : Lp ℝ 2 μ) : inner ℝ (lpMultiplier μ V a) a =
      ∫ x, χ.weight x*(a x)^2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpMultiplier_coe μ V a,boundedMultiplier_coe μ χ.weight
      χ.weight.continuous.measurable 1 (fun x => by
        rw [abs_of_nonneg (χ.bounds x).1]; exact (χ.bounds x).2)] with x hx hv
    change V x=χ.weight x at hv
    simp only [Real.inner_apply,hx,hv]
    ring
  have hh : Tendsto (fun k => inner ℝ (lpMultiplier μ V (ds k)) (ds k)) atTop
      (𝓝 (inner ℝ (lpMultiplier μ V d) d)) :=
    (((lpMultiplier μ V).continuous.tendsto d).comp hd).inner hd
  simpa only [he] using hh

theorem GoodLaplacianCutoff.bochner_source_tendsto
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C) (hC : 0 ≤ C)
    (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (us ds Gs : ℕ → SobolevSpace μ Q)
    (hds : ∀ k, IsWeakLaplacian μ Q (us k) (SobolevSpace.toLp μ Q (ds k)))
    (hGs : ∀ k, SobolevSpace.toLp μ Q (Gs k) =ᵐ[μ] localGamma μ Q (us k) (us k))
    (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u))
    (hdconv : Tendsto (fun k => SobolevSpace.toLp μ Q (ds k)) atTop (𝓝 d)) :
    Tendsto (fun k => -(1/2:ℝ)*energyForm μ Q (Gs k) χ.sobolev-
        weightedGamma μ Q (SobolevSpace.toLp μ Q χ.sobolev) (us k) (ds k)) atTop
      (𝓝 ((1/2:ℝ)*weightedGamma μ Q χ.laplacian u u+
        (∫ x, χ.weight x*(d x)^2 ∂μ)+weightedGamma μ Q d u χ.sobolev)) := by
  let P := weightedGammaCLM μ Q (Lp.aestronglyMeasurable χ.laplacian)
    (C := ⟨C/r^2,div_nonneg hC (sq_nonneg r)⟩)
    (by
      simp only [Real.norm_eq_abs]
      exact χ.laplacian_bound)
  have hp : Tendsto (fun k => weightedGamma μ Q χ.laplacian (us k) (us k)) atTop
      (𝓝 (weightedGamma μ Q χ.laplacian u u)) := by
    exact ((P.continuous.clm_apply continuous_id).tendsto u).comp hconv
  have hm := weightedGamma_joint_tendsto μ Q χ.sobolev L hus hu hconv hdconv
  have hh := ((hp.const_mul (1/2:ℝ)).add (χ.source_square_tendsto μ Q hdconv)).add hm
  apply hh.congr'
  filter_upwards [] with k
  exact (χ.bochner_source_identity μ Q (us k) (ds k) (Gs k) (hds k) (hGs k)).symm

end RegularPointCoordinates

end

end OAI
