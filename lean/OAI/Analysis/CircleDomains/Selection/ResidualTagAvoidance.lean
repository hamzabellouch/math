import OAI.Analysis.CircleDomains.Probability.ParametricNullTuples
import OAI.Analysis.CircleDomains.Selection.CodeResidualAvoidance

namespace OAI

/-! Independent later tags avoid the scalar-level null envelopes of an
earlier residual image. The product event is built from Borel envelopes. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_product_no_bad_tag_level (P : ProbabilityMeasure Ω)
    (d : PathCodeData X Y) (Q : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d Q ≪ tupleReference ω)
    (N : Ω → ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet {q : Ω × UnitAddCircle | q.2 ∈ N q.1 i})
    (hzero : ∀ᵐ a ∂(P : Measure Ω), ∀ i, volume (N a i) = 0) :
    ∀ᵐ p ∂((P : Measure Ω).prod (Q : Measure (BasePathCode d))),
      ∀ k q, p.2.val.2 k = Sum.inr q → ∀ j, q.2.2.1 j ∉ N p.1 (q.2.1 j) := by
  have hall : ∀ k, ∀ᵐ p ∂((P : Measure Ω).prod (Q : Measure (BasePathCode d))),
      (p.1, p.2.val.2 k) ∉ badSlotGraph N := by
    intro k
    let E : Set (Ω × BasePathCode d) := {p | (p.1, p.2.val.2 k) ∈ badSlotGraph N}
    have hE : MeasurableSet E := (measurableSet_badSlotGraph N hN).preimage
      (measurable_fst.prodMk ((measurable_pi_apply k).comp
        (measurable_snd.comp (measurable_subtype_coe.comp measurable_snd))))
    have hz : ((P : Measure Ω).prod (Q : Measure (BasePathCode d))) E = 0 := by
      rw [Measure.prod_apply hE]
      calc
        _ = ∫⁻ _a, (0 : ℝ≥0∞) ∂(P : Measure Ω) := by
          apply lintegral_congr_ae
          filter_upwards [hzero] with a ha
          have hNa : ∀ i, MeasurableSet (N a i) := fun i =>
            (hN i).preimage (measurable_const.prodMk measurable_id)
          have hgood := no_tag_level_in_null_set d Q ω hτ (N a) hNa ha
          have hnot : ∀ᵐ Γ ∂(Q : Measure (BasePathCode d)), Γ ∉ Prod.mk a ⁻¹' E := by
            filter_upwards [hgood] with Γ hΓ
            rintro ⟨q, hq, j, hj⟩
            exact hΓ k q hq j hj
          simpa only [ae_iff, not_not, ofPred_mem_eq] using hnot
        _ = 0 := by simp
    have hnot : ∀ᵐ p ∂((P : Measure Ω).prod (Q : Measure (BasePathCode d))), p ∉ E := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hz
    exact hnot
  filter_upwards [ae_all_iff.mpr hall] with p hp
  intro k q hq j hj
  exact hp k ⟨q, hq, j, hj⟩

end CircleDomainRigidity

end

end OAI
