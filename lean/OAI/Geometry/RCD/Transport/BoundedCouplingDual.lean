import OAI.Geometry.RCD.Sobolev.BoundedLocalRepresentative
import OAI.Geometry.RCD.Metric.EuclideanPairCost

namespace OAI

/-! # Optimality from local dual potentials on bounded endpoint supports -/

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
namespace RegularPointCoordinates

 theorem bounded_pair_cost_integrable {n : ℕ} {B : ℝ} (hB : 0≤B)
    (π : Measure (Euclidean n × Euclidean n)) [IsFiniteMeasure π]
    (hb : ∀ᵐ z ∂π, z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B) :
    Integrable (fun z => dist z.1 z.2^2) π := by
  apply ((boundedPairCost B).integrable π).congr
  filter_upwards [hb] with z hz
  exact boundedPairCost_eq hB hz.1 hz.2

 theorem bounded_pair_transportCost {n : ℕ} {B : ℝ} (hB : 0≤B)
    (π : Measure (Euclidean n × Euclidean n)) [IsFiniteMeasure π]
    (hb : ∀ᵐ z ∂π, z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B) :
    transportCost π=ENNReal.ofReal (∫ z, dist z.1 z.2^2 ∂π) := by
  rw [ofReal_integral_eq_lintegral_ofReal (bounded_pair_cost_integrable hB π hb)
    (Eventually.of_forall fun _ => sq_nonneg _)]
  simp only [transportCost,ENNReal.ofReal_pow dist_nonneg]

/-- Dual feasibility is needed only on the support of the endpoint marginals. -/
theorem bounded_coupling_optimal_of_dual {n : ℕ} {B : ℝ} (hB : 0≤B)
    (Q : ProbabilityMeasure (Euclidean n × Euclidean n))
    (hQ : ∀ᵐ z ∂(Q : Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B)
    {f g : Euclidean n → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (had : ∀ x∈closedBall 0 B, ∀ y∈closedBall 0 B, f x+g y≤dist x y^2/2)
    (hc : (∫ z, f z.1+g z.2 ∂(Q : Measure (Euclidean n × Euclidean n)))=
      (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))/2) :
    IsOptimalCoupling ((Q : Measure (Euclidean n × Euclidean n)).map Prod.fst)
      ((Q : Measure (Euclidean n × Euclidean n)).map Prod.snd) Q := by
  obtain ⟨F,hF⟩ := bounded_local_representative hB hf.lipschitzOnWith
  obtain ⟨G,hG⟩ := bounded_local_representative hB hg.lipschitzOnWith
  let H : (Euclidean n × Euclidean n) →ᵇ ℝ :=
    F.compContinuous ⟨Prod.fst,continuous_fst⟩+G.compContinuous ⟨Prod.snd,continuous_snd⟩
  have hsep (τ : Measure (Euclidean n × Euclidean n)) [IsFiniteMeasure τ] :
      (∫ z, H z ∂τ)=(∫ x, F x ∂τ.map Prod.fst)+(∫ y, G y ∂τ.map Prod.snd) := by
    have hFi : Integrable (fun z : Euclidean n × Euclidean n => F z.1) τ :=
      (F.compContinuous ⟨Prod.fst,continuous_fst⟩).integrable τ
    have hGi : Integrable (fun z : Euclidean n × Euclidean n => G z.2) τ :=
      (G.compContinuous ⟨Prod.snd,continuous_snd⟩).integrable τ
    calc
      (∫ z, H z ∂τ)=(∫ z, F z.1 ∂τ)+(∫ z, G z.2 ∂τ) := integral_add hFi hGi
      _ = _ := by
        rw [integral_map measurable_fst.aemeasurable F.continuous.aestronglyMeasurable,
          integral_map measurable_snd.aemeasurable G.continuous.aestronglyMeasurable]
  have hHQ : (∫ z, H z ∂(Q : Measure (Euclidean n × Euclidean n)))=
      (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))/2 := by
    rw [← hc]
    apply integral_congr_ae
    filter_upwards [hQ] with z hz
    exact congrArg₂ (·+·) (hF hz.1) (hG hz.2)
  refine ⟨rfl,rfl,?_⟩
  intro π hfst hsnd
  let : IsProbabilityMeasure π := coupling_probability_of_fst hfst
  have hfQ : ∀ᵐ x ∂(Q : Measure (Euclidean n × Euclidean n)).map Prod.fst,
      x∈closedBall (0:Euclidean n) B :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_closedBall).mpr
      (hQ.mono fun _ hz => hz.1)
  have hgQ : ∀ᵐ x ∂(Q : Measure (Euclidean n × Euclidean n)).map Prod.snd,
      x∈closedBall (0:Euclidean n) B :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_closedBall).mpr
      (hQ.mono fun _ hz => hz.2)
  have hπ : ∀ᵐ z ∂π, z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B := by
    have hh0 := ae_of_ae_map measurable_fst.aemeasurable (hfst.symm ▸ hfQ)
    have hh1 := ae_of_ae_map measurable_snd.aemeasurable (hsnd.symm ▸ hgQ)
    exact hh0.and hh1
  have heq : (∫ z, H z ∂(Q : Measure (Euclidean n × Euclidean n)))=∫ z, H z ∂π := by
    rw [hsep,hsep,hfst,hsnd]
  have hle : (∫ z, H z ∂π)≤(∫ z, dist z.1 z.2^2 ∂π)/2 := by
    rw [← integral_div]
    apply integral_mono_ae (H.integrable π) ((bounded_pair_cost_integrable hB π hπ).div_const 2)
    filter_upwards [hπ] with z hz
    change F z.1+G z.2≤_
    rw [hF hz.1,hG hz.2]
    exact had _ hz.1 _ hz.2
  rw [bounded_pair_transportCost hB _ hQ,bounded_pair_transportCost hB π hπ]
  apply ENNReal.ofReal_le_ofReal
  rw [← heq,hHQ] at hle
  linarith

end RegularPointCoordinates

end

end OAI
