import OAI.Probability.InvariantIsing.Cavity.CavityProjectionLimit
import OAI.Probability.InvariantIsing.Cavity.CavityConditioning

namespace OAI

/-! The exact nondegenerate Gaussian frame construction has the same
replica-projection limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavityConditionedFrameProjection_integral_tendsto {r q : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (v : (k : ℕ) → Fin r → Fin (N k) → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k i j => (∑ l, v k i l * v k j l) / (N k : ℝ))
      atTop (𝓝 Q)) (F : EuclideanSpace ℝ (Fin r × Fin q) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, F (cavityFrameProjection (v k) x)
      ∂cond (cavityGaussianRows q) (cavityGoodGram q (N k))) atTop
      (𝓝 (∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q Q))) := by
  have hd := cavityFrameProjection_tendsto_of_replicaGram (q := q) N hN v Q hQ
  have hu : Tendsto (fun k => ∫ x, F (cavityFrameProjection (v k) x) ∂cavityGaussianRows q)
      atTop (𝓝 (∫ y, F y ∂multivariateGaussian 0 (cavityReplicaCovariance q Q))) := by
    simpa only [id_eq] using
      ((tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
        hd.forall_aemeasurable hd.aemeasurable_limit).mp hd) F
  have hi (k : ℕ) : Integrable (fun x => F (cavityFrameProjection (v k) x))
      (cavityGaussianRows q) := by
    apply Integrable.of_bound
      (F.continuous.measurable.comp_aemeasurable (hd.forall_aemeasurable k)).aestronglyMeasurable
      ‖F‖
    exact ae_of_all _ (fun x => F.norm_coe_le_norm _)
  have hc := cavity_conditioning_tendsto (cavityGaussianRows q)
    (fun k => cavityGoodGram q (N k)) (fun k => measurableSet_cavityGoodGram q (N k))
    ((cavityGoodGram_probability_tendsto q).comp hN)
    (fun k x => F (cavityFrameProjection (v k) x)) hi ‖F‖
    (fun k x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (cavityFrameProjection (v k) x))
  convert hc.add hu using 1 <;> simp

end InvariantIsing

end

end OAI
