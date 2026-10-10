import OAI.Geometry.RCD.Transport.BoundedCouplingDual

namespace OAI

/-! # The sharp transport-cost upper bound for a translated probability law -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem optimal_translation_cost_le {n : ℕ} (α : ProbabilityMeasure (Euclidean n))
    (h : Euclidean n) (Q : ProbabilityMeasure (Euclidean n × Euclidean n))
    (hQ : IsOptimalCoupling (α : Measure (Euclidean n))
      (α.map (fun x => x+h) : Measure (Euclidean n)) (Q : Measure (Euclidean n × Euclidean n))) :
    (∫ y, dist y.1 y.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))≤‖h‖^2 := by
  let T := fun x : Euclidean n => (x,x+h)
  have hT : Measurable T := measurable_id.prodMk (measurable_id.add_const h)
  let P := α.map T
  have h0 : (P : Measure (Euclidean n × Euclidean n)).map Prod.fst=α := by
    rw [ProbabilityMeasure.toMeasure_map,Measure.map_map measurable_fst hT]
    change (α : Measure (Euclidean n)).map id=α
    exact Measure.map_id
  have h1 : (P : Measure (Euclidean n × Euclidean n)).map Prod.snd=
      (α.map (fun x => x+h) : Measure (Euclidean n)) := by
    rw [ProbabilityMeasure.toMeasure_map,Measure.map_map measurable_snd hT,
      ProbabilityMeasure.toMeasure_map]
    rfl
  have hcost : transportCost (P : Measure (Euclidean n × Euclidean n))=ENNReal.ofReal (‖h‖^2) := by
    rw [transportCost,ProbabilityMeasure.toMeasure_map,lintegral_map
      ((measurable_fst.dist measurable_snd).ennreal_ofReal.pow_const 2) hT]
    have hd (x : Euclidean n) : dist x (x+h)=‖h‖ := by simp [dist_eq_norm]
    simp only [T,hd,lintegral_const,measure_univ,mul_one,ENNReal.ofReal_pow (norm_nonneg h)]
  have hb := (hQ.2.2 (P : Measure (Euclidean n × Euclidean n)) h0 h1).trans_eq hcost
  have hi : Integrable (fun y : Euclidean n × Euclidean n => dist y.1 y.2^2)
      (Q : Measure (Euclidean n × Euclidean n)) := by
    refine ⟨((continuous_fst.dist continuous_snd).pow 2).aestronglyMeasurable,?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr
    simp_rw [ENNReal.ofReal_pow dist_nonneg]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)
  simp_rw [ENNReal.ofReal_pow dist_nonneg] at he
  rw [transportCost,← he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖h‖)).mp hb

end RegularPointCoordinates

end

end OAI
