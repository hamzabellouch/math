import OAI.Analysis.CircleDomains.Probability.OccupationProduct
import OAI.Analysis.CircleDomains.Topology.BallPairKernel

namespace OAI

/-! The proximity integral of independent physical path occupations is
controlled by their local square energies. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

def codePairProximity (d e : PathCodeData X Y) (A : Set Y) (a : ℝ≥0)
    (p : BasePathCode d × BasePathCode e) : ℝ≥0∞ :=
  ∫⁻ z, ballPairKernel A a z ∂(baseCodeOccupation d p.1).prod (baseCodeOccupation e p.2)

theorem measurable_codePairProximity (d e : PathCodeData X Y)
    (hd : IsOpen d.quotientDomain) (he : IsOpen e.quotientDomain)
    (A : Set Y) (hA : MeasurableSet A) (a : ℝ≥0) :
    Measurable (codePairProximity d e A a) :=
  (Measure.measurable_lintegral (measurable_ballPairKernel A hA a)).comp
    (measurable_finite_measure_product _ _ (measurable_baseCodeOccupation d hd)
      (measurable_baseCodeOccupation e he))

theorem mean_codePairProximity_le (d e : PathCodeData X Y)
    (hd : IsOpen d.quotientDomain) (he : IsOpen e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (σ : Measure Y) [SFinite σ] (g h : Y → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h)
    (hP : meanCodeOccupation d P = σ.withDensity g)
    (hQ : meanCodeOccupation e Q = σ.withDensity h)
    (A : Set Y) (hA : MeasurableSet A) {a : ℝ≥0} (ha : a ≠ 0) {C E : ℝ≥0∞}
    (hball : ∀ x ∈ A, σ (Metric.ball x (2 * a)) ≤ C * (a : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in A, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x in A, h x ^ 2 ∂σ) ≤ E) :
    (∫⁻ p, codePairProximity d e A a p
      ∂(P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))) ≤ C * E := by
  change (∫⁻ p, ∫⁻ z, ballPairKernel A a z
    ∂(baseCodeOccupation d p.1).prod (baseCodeOccupation e p.2)
    ∂(P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))) ≤ C * E
  rw [mean_code_pair_occupation d e hd he P Q _ (measurable_ballPairKernel A hA a),
    hP, hQ, prod_withDensity hg hh,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : Y × Y => g z.1 * h z.2) from
        (hg.comp measurable_fst).mul (hh.comp measurable_snd))
      (measurable_ballPairKernel A hA a)]
  have hb := localized_ball_pair_energy_bound σ A hA ha g h hg hh hball hgE hhE
  simpa only [Pi.mul_apply, Function.comp_def, mul_comm] using hb

end CircleDomainRigidity

end

end OAI
