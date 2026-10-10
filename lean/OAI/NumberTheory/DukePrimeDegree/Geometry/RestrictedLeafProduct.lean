import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalProduct
import OAI.NumberTheory.PrimePackets.ConditionalFibers

namespace OAI

/-! # Product measures from projectively equal leaf restrictions -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma anchorNormalize_restrict_finite (ν : Measure ℝ) (J : Set ℝ) :
    IsFiniteMeasure ((anchorNormalize ν J).restrict J) := by
  constructor
  change ((ν J)⁻¹ • ν).restrict J univ < ∞
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.smul_apply,smul_eq_mul]
  exact (ENNReal.inv_mul_le_one (ν J)).trans_lt ENNReal.one_lt_top

theorem restricted_eq_prod_of_projective_leaf_restrictions
    {B : Type*} [MeasurableSpace B] (μ : Measure (B × ℝ)) [IsFiniteMeasure μ]
    (J : Set ℝ) (hJ : MeasurableSet J) (leaf : B → Measure ℝ) (ν : Measure ℝ)
    (hres : ∀ᵐ w ∂μ.fst, (μ.condKernel w).restrict J = (leaf w).restrict J)
    (heq : ∀ᵐ w ∂μ.fst, anchorNormalize (leaf w) J = anchorNormalize ν J) :
    μ.restrict (univ ×ˢ J) = (μ.restrict (univ ×ˢ J)).fst.prod
      ((anchorNormalize ν J).restrict J) := by
  let : IsFiniteMeasure ((anchorNormalize ν J).restrict J) := anchorNormalize_restrict_finite ν J
  apply eq_prod_of_constant_real_conditionals
  have hbase : (μ.restrict (univ ×ˢ J)).fst ≪ μ.fst :=
    Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)
  have hcond := conditional_restrict_normalized μ (univ ×ˢ J) (MeasurableSet.univ.prod hJ)
  filter_upwards [hcond,hbase.ae_le hres,hbase.ae_le heq] with w hc hr he
  have hfiber : Prod.mk w ⁻¹' (univ ×ˢ J : Set (B × ℝ)) = J := by
    ext t
    simp
  rw [hfiber] at hc
  rw [hc.2]
  rw [←anchorNormalize_restrict_comm _ hJ subset_rfl,hr,
    anchorNormalize_restrict_comm _ hJ subset_rfl,he]

end DukePrimeDegree

end

end OAI
