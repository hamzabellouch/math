import OAI.Analysis.CircleDomains.Probability.CompactLawSplit
import OAI.Analysis.CircleDomains.Modulus.ConfigurationAtomicNorm
import OAI.Analysis.CircleDomains.Sobolev.ConfigurationHitIntegral

namespace OAI

/-! A finite split for separated hit configurations. Nonsmallness supplies
a candidate against the mean configuration measure; its atomic norm bound
and the hit-integral identity give the compact-law split. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_hit_configuration_split
    {X Z : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
    [TopologicalSpace Z] (law : Z → ProbabilityMeasure C(PathTime, X))
    (hlaw : Continuous law) {A : Set Z} {C ε r : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hr : 0 < r) (n : ℕ) [Nonempty (HitConfiguration X n r)]
    (hA : ¬HitTestSmall law C A) :
    ∃ (k : ℕ) (z : Fin k → Z) (w : Fin k → ℝ),
      (∀ i, z i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ p : HitConfiguration X n r, ∑ i, w i * weightedConfigurationHits law (z i) p ≤ C + ε := by
  have hfixed (z : Z) : UpperSemicontinuous (weightedConfigurationHits law z : HitConfiguration X n r → ℝ) :=
    (weightedConfigurationHits_upperSemicontinuous hlaw n r).comp
      (continuous_const.prodMk continuous_id)
  apply exists_finite_compact_law_split (fun z p => weightedConfigurationHits law z p) A
    (fun z _ => hfixed z) (fun z _ p => weightedConfigurationHits_nonneg law z p)
    (M := (n : ℝ) + 1) (by positivity)
    (fun z _ p => (weightedConfigurationHits_le_card law z p).trans (by linarith)) hε
  intro P
  obtain ⟨z, hz, hb⟩ := exists_test_law_for_atomic_measure law hC hA
    (meanConfigurationMeasure P) (meanConfigurationMeasure_hasAtomicSquareBound hr P)
  refine ⟨z, hz, ?_⟩
  rwa [integral_meanConfigurationMeasure_hit P (law z)] at hb

end CircleDomainRigidity

end

end OAI
