import OAI.Analysis.CircleDomains.Probability.MarkedHitLaws
import OAI.Analysis.CircleDomains.Selection.HitConfigurations

namespace OAI

/-! Separated configurations lie in the dust test space, while their hit
probabilities come from paths in the ambient space. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)] (ι : C(X, Y))

def weightedConfigurationHits (law : Z → ProbabilityMeasure C(PathTime, Y))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) : ℝ :=
  ∑ i, (p.val.2 i : ℝ) * pathHitReal ι (law z) (p.val.1 i)

theorem weightedConfigurationHits_nonneg (law : Z → ProbabilityMeasure C(PathTime, Y))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) :
    0 ≤ weightedConfigurationHits ι law z p :=
  Finset.sum_nonneg fun i _ => mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg ι _ _)

theorem weightedConfigurationHits_le_card (law : Z → ProbabilityMeasure C(PathTime, Y))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) :
    weightedConfigurationHits ι law z p ≤ n := by
  calc
    ∑ i, (p.val.2 i : ℝ) * pathHitReal ι (law z) (p.val.1 i) ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (mul_le_mul (p.val.2 i).property.2 (pathHitReal_le_one ι _ _)
        (pathHitReal_nonneg ι _ _) (by norm_num)).trans_eq (one_mul 1)
    _ = n := by simp

variable [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, Y)] [TopologicalSpace Z]

theorem weightedConfigurationHits_upperSemicontinuous
    {law : Z → ProbabilityMeasure C(PathTime, Y)} (hlaw : Continuous law) (n : ℕ) (r : ℝ) :
    UpperSemicontinuous (fun q : Z × HitConfiguration X n r =>
      weightedConfigurationHits ι law q.1 q.2) := by
  apply upperSemicontinuous_sum
  intro i _
  have hw : Continuous (fun q : Z × HitConfiguration X n r => (q.2.val.2 i : ℝ)) :=
    by fun_prop
  have hh : UpperSemicontinuous (fun q : Z × HitConfiguration X n r =>
      pathHitReal ι (law q.1) (q.2.val.1 i)) :=
    (pathHitReal_upperSemicontinuous ι).comp
      ((hlaw.comp continuous_fst).prodMk (by fun_prop))
  exact upperSemicontinuous_nonnegative_mul hw.upperSemicontinuous hh
    (fun q => (q.2.val.2 i).property.1) (fun _ => pathHitReal_nonneg ι _ _)

end CircleDomainRigidity.MarkedHit

end

end OAI
