import OAI.Geometry.RCD.Sobolev.SourceMassDifferenceEnergy
import OAI.Geometry.RCD.Sobolev.WeightedWeakCauchyEnergy
import OAI.Geometry.RCD.Sobolev.WeightedGammaLocality

namespace OAI

/-! # Strong local gradients from uniform values and bounded source mass

The source representatives may differ outside the working set from the
bounded Sobolev sequence used for weak compactness.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_source_strong_gradient
    (u w : ℕ → SobolevSpace μ Q) (f η : SobolevSpace μ Q) (d : ℕ → Lp ℝ 2 μ)
    (hd : ∀ k, IsWeakLaplacian μ Q (u k) (d k))
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (huw : ∀ k, SobolevSpace.toLp μ Q (u k) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q (w k))
    (hweak : ∀ ℓ : SobolevSpace μ Q →L[ℝ] ℝ,
      Tendsto (fun k => ℓ (w k)) atTop (𝓝 (ℓ f)))
    {v : X → ℝ} {L B M : ℝ≥0}
    (hv : LipschitzWith L v) (hs : HasCompactSupport v)
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hzero : ∀ x ∉ Ω, v x = 0)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ Q η x| ≤ M)
    {A : ℝ} (hA : 0 ≤ A)
    (hdi : ∀ k, Integrable (fun x => (v x)^2*|d k x|) μ)
    (hdA : ∀ k, (∫ x, (v x)^2*|d k x| ∂μ) ≤ A)
    (hvalue : ∀ D : ℝ, 0 < D → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      ∀ᵐ x ∂μ, v x ≠ 0 →
        |SobolevSpace.toLp μ Q (u i) x-SobolevSpace.toLp μ Q (u j) x| ≤ D) :
    Tendsto (fun k => weightedGamma μ Q (fun x => (v x)^2) (w k-f) (w k-f)) atTop (𝓝 0) := by
  let E := ∫ x, (SobolevSpace.minimalSlope μ Q η x)^2 ∂μ
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hv2 : AEStronglyMeasurable (fun x => (v x)^2) μ := hv.continuous.aestronglyMeasurable.pow 2
  have hb2 : ∀ᵐ x ∂μ, ‖(v x)^2‖ ≤ (B^2 : ℝ≥0) := Eventually.of_forall fun x => by
    simpa only [NNReal.coe_pow,Real.norm_eq_abs,abs_pow,sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
  have hv0 : ∀ᵐ x ∂μ, 0 ≤ (v x)^2 := Eventually.of_forall fun x => sq_nonneg _
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let D := min 1 (ε/(2*(4*A+4*E+1)))
  have hden : 0 < 2*(4*A+4*E+1) := by positivity
  have hD : 0 < D := lt_min zero_lt_one (div_pos hε hden)
  have hD1 : D ≤ 1 := min_le_left _ _
  have hDε : D*(2*(4*A+4*E+1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have herr : 4*D*A+4*D^2*E < ε := by
    have hs : D^2 ≤ D := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs hE
    nlinarith
  obtain ⟨N,hN⟩ := hvalue D hD
  refine ⟨N,fun i hi => ?_⟩
  have hpair : ∀ᶠ j in atTop,
      weightedGamma μ Q (fun x => (v x)^2) (w i-w j) (w i-w j) ≤ 4*D*A+4*D^2*E := by
    filter_upwards [eventually_ge_atTop N] with j hj
    have hdiff : SobolevSpace.toLp μ Q (u i-u j) =ᵐ[μ.restrict Ω]
        SobolevSpace.toLp μ Q (w i-w j) := by
      simp only [map_sub]
      filter_upwards [huw i,huw j,
        ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q (u i)) (SobolevSpace.toLp μ Q (u j))),
        ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q (w i)) (SobolevSpace.toLp μ Q (w j)))]
        with x ha hb hc hd
      rw [hc,hd]
      simp only [Pi.sub_apply,ha,hb]
    rw [← weightedGamma_congr_on μ Q hΩ hdiff hdiff (fun x => (v x)^2)
      (fun x hx => by rw [hzero x hx]; norm_num)]
    exact source_mass_difference_energy μ Q (u i) (u j) η (d i) (d j) (hd i) (hd j)
      hv hs hb hn hη hgrad hD.le hA (hN i hi j hj) (hdi i) (hdi j) (hdA i) (hdA j)
  have hbound := weighted_energy_le_of_weak_cauchy μ Q w f hweak hv2 hb2 hv0 i hpair
  have hnonneg := weightedGamma_nonneg_of_weight μ Q hv0 (w i-f)
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg] using hbound.trans_lt herr

end RegularPointCoordinates

end

end OAI
