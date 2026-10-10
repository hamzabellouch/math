import OAI.Analysis.CircleDomains.Topology.PathTags
import OAI.Analysis.CircleDomains.Topology.ClosedTimeCounts
import OAI.Analysis.CircleDomains.Topology.PathTolls

namespace OAI

/-! Actual residual visit multiplicities and tolls on closed test intervals. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def residualVisitRelation (B : Set X) (I : Set PathTime) :
    Set ((TaggedPath X × X) × PathTime) :=
  {q | q.2 ∈ residualTimes B q.1.1 ∧ q.2 ∈ I ∧ q.1.1.1 q.2 = q.1.2}

theorem isClosed_residualVisitRelation {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) : IsClosed (residualVisitRelation B I) :=
  ((isClosed_residualTimeGraph hB).preimage
    (continuous_fst.fst.prodMk continuous_snd)).inter
      ((hI.preimage continuous_snd).inter (isClosed_eq
        (continuous_eval.comp (continuous_fst.fst.fst.prodMk continuous_snd)) continuous_fst.snd))

def residualVisitCount (B : Set X) (I : Set PathTime) (Γ : TaggedPath X) (x : X) : ℝ≥0∞ :=
  timeCount (residualVisitRelation B I) (Γ, x)

def residualToll (B : Set X) (I : Set PathTime) (m : X → ℝ≥0∞) (Γ : TaggedPath X) : ℝ≥0∞ :=
  ∑' t : PathTime, if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0

theorem residualToll_eq_visits (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = ∑' x, m x * residualVisitCount B I Γ x := by
  rw [residualToll, ← ENNReal.tsum_fiberwise
    (fun t => if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0) Γ.1]
  apply tsum_congr
  intro x
  rw [residualVisitCount, timeCount, ← ENNReal.tsum_mul_left,
    tsum_subtype (Γ.1 ⁻¹' {x})
      (fun t : PathTime => if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0)]
  apply tsum_congr
  intro t
  by_cases he : Γ.1 t = x <;>
    by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ I <;>
      simp [Set.indicator, residualVisitRelation, he, ht]

theorem residualToll_eq_support (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = ∑' x : Function.support m, m x * residualVisitCount B I Γ x := by
  rw [residualToll_eq_visits]
  symm
  apply tsum_subtype_eq_of_support_subset
    (f := fun x : X => m x * residualVisitCount B I Γ x)
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_residualVisitCount {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) :
    Measurable (fun q : TaggedPath X × X => residualVisitCount B I q.1 q.2) :=
  measurable_timeCount (isClosed_residualVisitRelation hB hI)

theorem measurable_residualToll {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {m : X → ℝ≥0∞}
    (hm : (Function.support m).Countable) : Measurable (residualToll B I m) := by
  let : Countable (Function.support m) := hm.to_subtype
  change Measurable (fun Γ => residualToll B I m Γ)
  simp_rw [residualToll_eq_support]
  exact Measurable.tsum fun x => measurable_const.mul
    ((measurable_residualVisitCount hB hI).comp (measurable_id.prodMk measurable_const))

theorem measurable_residualToll_of_summable_sq {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {m : X → ℝ}
    (hm : Summable (fun x => (m x) ^ 2)) :
    Measurable (residualToll B I (fun x => ENNReal.ofReal (m x))) :=
  measurable_residualToll hB hI (countable_support_of_summable_sq hm)

end CircleDomainRigidity

end

end OAI
