import OAI.Analysis.CircleDomains.Probability.ResidualTailNull
import OAI.Analysis.CircleDomains.Selection.SquareVisitTolls

namespace OAI

/-! The stored rational-interval constraints give null residual-incidence
envelopes under the actual square bounds on visits. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

private def rationalStart : RationalPathTime := ⟨0, by norm_num⟩
private def rationalEnd : RationalPathTime := ⟨1, by norm_num⟩

private theorem rationalStart_eq : rationalStart.toTime = (⊥ : PathTime) := by
  apply Subtype.ext
  norm_num [rationalStart, RationalPathTime.toTime]

private theorem rationalEnd_eq : rationalEnd.toTime = (⊤ : PathTime) := by
  apply Subtype.ext
  norm_num [rationalEnd, RationalPathTime.toTime]

theorem baseCode_prior_bound (d : PathCodeData X Y) (Γ : BasePathCode d) (i n : ℕ) :
    ResidualIncidenceBound d.dust univ pathHitSet (d.priorDeletions i n)
      (d.priorLaws i) (priorHitMass (d.priorLaws i)) Γ.val := by
  have h := Γ.property.1.2.2.1 i n rationalStart rationalEnd
  simpa only [rationalStart_eq, rationalEnd_eq, Icc_bot_top] using h

theorem baseCode_level_bound (d : PathCodeData X Y) (Γ : BasePathCode d) (i n : ℕ) :
    ResidualIncidenceBound d.dust univ (d.levels i) (d.flagDeletions n)
      volume (d.levelWeights i) Γ.val := by
  have h := Γ.property.1.2.2.2.1 i n rationalStart rationalEnd
  simpa only [rationalStart_eq, rationalEnd_eq, Icc_bot_top] using h

variable [BorelSpace X] [SecondCountableTopology X] [BorelSpace C(PathTime, X)]

theorem ae_code_boundaryToll_finite (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (m : X → ℝ≥0∞)
    (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), boundaryToll Γ.val.1 m < ∞ := by
  have h := ae_boundaryToll_finite (codePathLaw d P) m hm hweight hvisits
  exact (ae_map_iff (measurable_codePath d).aemeasurable
    (measurableSet_lt (measurable_boundaryToll hm) measurable_const)).mp h

theorem ae_code_prior_envelope_null (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (hm : (support (priorHitMass (d.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (priorHitMass (d.priorLaws i)) =>
      priorHitMass (d.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (priorHitMass (d.priorLaws i)) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (priorHitMass (d.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ d.priorDeletions i n) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), (d.priorLaws i)
      (⋂ n, {η | (Γ.val, η) ∈ residualIncidence d.dust univ pathHitSet
        (d.priorDeletions i n)}) = 0 := by
  filter_upwards [ae_code_boundaryToll_finite d P _ hm hweight hvisits] with Γ hΓ
  exact residual_incidence_envelope_null d.dust univ pathHitSet _ _ hm _ hcover
    Γ.val hΓ (baseCode_prior_bound d Γ i)

theorem ae_code_level_envelope_null (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i),
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), volume
      (⋂ n, {t | (Γ.val, t) ∈ residualIncidence d.dust univ (d.levels i)
        (d.flagDeletions n)}) = 0 := by
  filter_upwards [ae_code_boundaryToll_finite d P _ hm hweight hvisits] with Γ hΓ
  exact residual_incidence_envelope_null d.dust univ (d.levels i) _ _ hm _ hcover
    Γ.val hΓ (baseCode_level_bound d Γ i)

end CircleDomainRigidity

end

end OAI
