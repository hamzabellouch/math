import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Analysis.RCDHeat.WeightedGradientConvex

namespace OAI

/-! # The signed first variation for a compact quadratic contact potential -/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem compact_contact_first_variation (hspace : IsGeodesicSpace X)
    (p : X) {ψ : X → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ)
    {R : ℝ} (hzero : ∀ x, R < dist p x → ψ x = 0)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (hc : ∀ᵐ γ ∂π, hopfLax (-ψ) 1 (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) :
    ∃ u : SobolevSpace μ hQ,
      (hopfLax (-ψ) 1 =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) = dist (γ 0) (γ 1)) ∧
      ∀ g : SobolevSpace μ hQ,
        Tendsto (planInitialSecant π (SobolevSpace.toLp μ hQ g)) (𝓝[>] (0:ℝ))
          (𝓝 (-weightedGradientPair μ hQ (π.map (fun γ => γ 0)) u g)) := by
  have hpos : (0 : ℝ) < 1 := by norm_num
  have hnzero (x : X) (hx : R < dist p x) : (-ψ) x = 0 := by
    simp only [Pi.neg_apply,hzero x hx,neg_zero]
  have hχ := hopfLax_lipschitz hψ.neg hspace hpos
  have hχs := hopfLax_hasCompactSupport hψ.neg p R hnzero hpos
  let u := SobolevSpace.ofLipschitzCompact μ hQ hχ hχs
  have hurep : hopfLax (-ψ) 1 =ᵐ[μ] SobolevSpace.toLp μ hQ u :=
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hχ hχs).symm
  have had (x y : X) : hopfLax (-ψ) 1 x+ψ y ≤ dist x y^2/2 := by
    have hh := hopfLax_le_cost hψ.neg hpos x y
    simp only [Pi.neg_apply,mul_one] at hh
    linarith
  have hbound : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ hopfLeftRadius (-ψ) x :=
    hopfLeftRadius_minimalSlope_bound_proper μ hQ hψ.neg hspace p R hnzero
  have hstart : ∀ᵐ γ ∂π,
      SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ hopfLeftRadius (-ψ) (γ 0) :=
    ae_of_ae_map (measurable_path_eval 0).aemeasurable
      (hbound.filter_mono (Measure.absolutelyContinuous_of_le_smul (hcomp 0)).ae_le)
  have hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) ≤ dist (γ 0) (γ 1) := by
    filter_upwards [hstart,hc] with γ hγ he
    apply hγ.trans (hopfLeftRadius_le_minimizer hψ.neg ?_)
    change hopfLax (-ψ) 1 (γ 0) = -ψ (γ 1)+dist (γ 0) (γ 1)^2/(2*1)
    linarith
  refine ⟨u,hurep,?_,?_⟩
  · exact (SobolevSpace.minimalSlope_isRelaxed μ hQ u).kantorovich_gradient_eq_displacement
      μ π hgeo hC hcomp hD hurep had hc hb
  · intro g
    exact kantorovich_signed_first_variation μ hQ π hgeo hC hcomp hD u g hurep had hc hb

end RegularPointCoordinates

end

end OAI
