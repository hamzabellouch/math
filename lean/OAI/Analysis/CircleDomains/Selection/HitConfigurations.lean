import OAI.Analysis.CircleDomains.Modulus.HitNormTopology

namespace OAI

/-! Compact spaces of separated weighted point configurations, and the actual
uniform-neighborhood estimate for weighted hit probabilities over each such space. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev HitConfigurationAmbient (X : Type*) (n : ℕ) :=
  (Fin n → X) × (Fin n → Icc (0 : ℝ) 1)

def hitConfigurationSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    Set (HitConfigurationAmbient X n) :=
  {p | (∑ i, (p.2 i : ℝ) ^ 2) ≤ 1 ∧
    ∀ i j, i ≠ j → r ≤ dist (p.1 i) (p.1 j)}

theorem isClosed_hitConfigurationSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    IsClosed (hitConfigurationSet (X := X) n r) := by
  have h1 : IsClosed {p : HitConfigurationAmbient X n | (∑ i, (p.2 i : ℝ) ^ 2) ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {p : HitConfigurationAmbient X n |
      ∀ i j, i ≠ j → r ≤ dist (p.1 i) (p.1 j)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)
  exact h1.inter h2

abbrev HitConfiguration (X : Type*) [MetricSpace X] (n : ℕ) (r : ℝ) :=
  hitConfigurationSet (X := X) n r

instance {X : Type*} [MetricSpace X] [CompactSpace X] (n : ℕ) (r : ℝ) :
    CompactSpace (HitConfiguration X n r) :=
  isCompact_iff_compactSpace.mp (isClosed_hitConfigurationSet n r).isCompact

def weightedConfigurationHits {X Z : Type*} [MetricSpace X]
    [MeasurableSpace C(PathTime, X)] (law : Z → ProbabilityMeasure C(PathTime, X))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) : ℝ :=
  ∑ i, (p.val.2 i : ℝ) * pathHitReal (law z) (p.val.1 i)

theorem weightedConfigurationHits_nonneg {X Z : Type*} [MetricSpace X]
    [MeasurableSpace C(PathTime, X)] (law : Z → ProbabilityMeasure C(PathTime, X))
    {n : ℕ} {r : ℝ} (z : Z) (p : HitConfiguration X n r) :
    0 ≤ weightedConfigurationHits law z p :=
  Finset.sum_nonneg fun i _ => mul_nonneg (p.val.2 i).property.1 (pathHitReal_nonneg _ _)

theorem weightedConfigurationHits_upperSemicontinuous
    {X Z : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
    [TopologicalSpace Z] {law : Z → ProbabilityMeasure C(PathTime, X)}
    (hlaw : Continuous law) (n : ℕ) (r : ℝ) :
    UpperSemicontinuous (fun q : Z × HitConfiguration X n r =>
      weightedConfigurationHits law q.1 q.2) := by
  apply upperSemicontinuous_sum
  intro i _
  have hw : Continuous (fun q : Z × HitConfiguration X n r => (q.2.val.2 i : ℝ)) :=
    by fun_prop
  have hh : UpperSemicontinuous (fun q : Z × HitConfiguration X n r =>
      pathHitReal (law q.1) (q.2.val.1 i)) :=
    pathHitReal_upperSemicontinuous.comp
      ((hlaw.comp continuous_fst).prodMk (by fun_prop))
  exact upperSemicontinuous_nonnegative_mul hw.upperSemicontinuous hh
    (fun q => (q.2.val.2 i).property.1) (fun _ => pathHitReal_nonneg _ _)

/-- A uniform strict configuration bound at a center holds throughout some open
neighborhood of that center. No continuity of the individual hit functions is assumed. -/
theorem exists_open_uniform_configuration_bound
    {X Z : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
    [TopologicalSpace Z] {law : Z → ProbabilityMeasure C(PathTime, X)}
    (hlaw : Continuous law) {n : ℕ} {r c : ℝ} {z : Z}
    (hz : ∀ p : HitConfiguration X n r, weightedConfigurationHits law z p < c) :
    ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧
      ∀ y ∈ U, ∀ p : HitConfiguration X n r, weightedConfigurationHits law y p < c := by
  exact ⟨_, isOpen_forall_compact_upper_bound
    (weightedConfigurationHits_upperSemicontinuous hlaw n r) c, hz, fun _ h => h⟩

end CircleDomainRigidity

end

end OAI
