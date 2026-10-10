import OAI.Geometry.RCD.Metric.IntervalMassDrop
import OAI.Geometry.RCD.Metric.SeparatedPairRestriction
import OAI.Analysis.RCDHeat.DynamicalPlan

namespace OAI

/-! # Measurable common prefixes of paired paths -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def pathAgreement (t : ℝ) : Set (C(Time,X)×C(Time,X)) :=
  {z | ∀ r : Time, (r:ℝ)≤t → z.1 r=z.2 r}

theorem antitone_pathAgreement : Antitone (pathAgreement (X:=X)) := by
  intro s t hst z hz r hr
  exact hz r (hr.trans hst)

theorem isClosed_pathAgreement (t : ℝ) : IsClosed (pathAgreement (X:=X) t) := by
  change IsClosed {z : C(Time,X)×C(Time,X) | ∀ r : Time, (r:ℝ)≤t → z.1 r=z.2 r}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro r
  apply isClosed_iInter
  intro _
  exact isClosed_eq ((continuous_eval_const r).comp continuous_fst)
    ((continuous_eval_const r).comp continuous_snd)

variable [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem measurableSet_pathAgreement (t : ℝ) : MeasurableSet (pathAgreement (X:=X) t) :=
  (isClosed_pathAgreement t).measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_path_agreement_mass_drop (σ : Measure (C(Time,X)×C(Time,X)))
    [IsFiniteMeasure σ] {a b : ℝ} (hab : a≤b) {n : ℕ} (hn : 0<n) :
    ∃ k<n, (σ.real (pathAgreement a)-σ.real (pathAgreement b))/(n:ℝ)≤
      σ.real (pathAgreement (intervalGrid a b n k) \ pathAgreement (intervalGrid a b n (k+1))) :=
  exists_large_nested_mass_drop σ measurableSet_pathAgreement antitone_pathAgreement hab hn

omit [BorelSpace X] [SeparableSpace X] in
theorem restricted_paths_common_past (σ : Measure (C(Time,X)×C(Time,X)))
    {S : Set (C(Time,X)×C(Time,X))} (hS : MeasurableSet S)
    {a : ℝ} (hSa : S⊆pathAgreement a) (r : Time) (hr : (r:ℝ)≤a) :
    (σ.restrict S).map (fun z => z.1 r)=(σ.restrict S).map (fun z => z.2 r) := by
  apply Measure.map_congr
  exact (ae_restrict_mem hS).mono fun z hz => hSa hz r hr

end RegularPointCoordinates

end

end OAI
