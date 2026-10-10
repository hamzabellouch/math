import OAI.Analysis.CircleDomains.Probability.ConfigurationMeasures
import OAI.Analysis.CircleDomains.Selection.MarkedConfigurations

namespace OAI

/-! Hit integrals against the actual mean configuration measure are precisely
the expected weighted hit counts. This identifies the two sides of the finite
split without replacing the configuration measure by abstract test data. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  {n : ℕ} {r : ℝ} (ι : C(X, Y))

theorem integral_meanConfigurationMeasure_hit
    (P : ProbabilityMeasure (HitConfiguration X n r)) (μ : ProbabilityMeasure C(PathTime, Y)) :
    ∫ x, pathHitReal ι μ x ∂meanConfigurationMeasure P =
      ∫ p, ∑ i, (p.val.2 i : ℝ) * pathHitReal ι μ (p.val.1 i)
        ∂(P : Measure (HitConfiguration X n r)) := by
  let v : HitConfiguration X n r → ℝ := fun p =>
    ∑ i, (p.val.2 i : ℝ) * pathHitReal ι μ (p.val.1 i)
  have hv0 (p : HitConfiguration X n r) : 0 ≤ v p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg ι _ _)
  have hvm : Measurable v := by
    apply Finset.measurable_sum
    intro i _
    exact (by fun_prop : Continuous (fun p : HitConfiguration X n r => (p.val.2 i : ℝ))).measurable.mul
      (((measurable_pathHitProbability_point ι μ).comp
        (by fun_prop : Continuous (fun p : HitConfiguration X n r => p.val.1 i)).measurable).ennreal_toReal)
  have hpoint (p : HitConfiguration X n r) :
      (∑ i, ENNReal.ofReal (p.val.2 i : ℝ) * pathHitProbability ι μ (p.val.1 i)) =
        ENNReal.ofReal (v p) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg ι _ _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (p.val.2 i).property.1, pathHitReal,
      ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one ι _ _) (by simp)))]
  calc
    ∫ x, pathHitReal ι μ x ∂meanConfigurationMeasure P =
        (∫⁻ x, pathHitProbability ι μ x ∂meanConfigurationMeasure P).toReal :=
      integral_toReal (measurable_pathHitProbability_point ι μ).aemeasurable
        (Eventually.of_forall fun x => lt_of_le_of_lt (pathHitProbability_le_one ι _ _) (by simp))
    _ = (∫⁻ p, ENNReal.ofReal (v p) ∂(P : Measure (HitConfiguration X n r))).toReal := by
      rw [lintegral_meanConfigurationMeasure P (measurable_pathHitProbability_point ι μ)]
      simp_rw [hpoint]
    _ = ∫ p, v p ∂(P : Measure (HitConfiguration X n r)) := by
      have he := integral_toReal (μ := (P : Measure (HitConfiguration X n r)))
        hvm.ennreal_ofReal.aemeasurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
      simpa only [ENNReal.toReal_ofReal (hv0 _)] using he.symm

end CircleDomainRigidity.MarkedHit

end

end OAI
