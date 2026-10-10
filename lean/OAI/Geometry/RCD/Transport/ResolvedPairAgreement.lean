import OAI.Geometry.RCD.Transport.ResolvedBranchMeasure

namespace OAI

/-! # The resolved pair has a single initial interval of agreement -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def resolvedPathPair (q : Time) (z : C(Time,X)×C(Time,X)) : C(Time,X)×C(Time,X) :=
  (z.1,resolvePathBranch q z)

theorem resolved_pair_agreement_iff (q : Time) (z : C(Time,X)×C(Time,X))
    (hz : z.1 0=z.2 0) {t : Time} (htq : t≤q) :
    resolvedPathPair q z∈pathAgreement (t:ℝ) ↔ t≤lastPathAgreement q z := by
  constructor
  · intro ht
    by_contra h
    exact resolvePathBranch_ne_after q z hz (lt_of_not_ge h) htq (ht t le_rfl)
  · intro ht r hr
    change z.1 r=resolvePathBranch q z r
    rw [resolvePathBranch_apply q z hz,ite_eq_left ((show r≤t from hr).trans ht)]

theorem resolved_pair_distinct_at (q : Time) (z : C(Time,X)×C(Time,X))
    (hz : z.1 0=z.2 0) (hq : z.1 q≠z.2 q) :
    lastPathAgreement q z<q := by
  apply lt_of_le_of_ne (lastPathAgreement_le q z)
  intro he
  apply hq
  simpa only [he] using lastPathAgreement_eq q hz

variable [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem measurable_resolvedPathPair (q : Time) : Measurable (resolvedPathPair (X:=X) q) :=
  measurable_fst.prodMk (measurable_resolvePathBranch q)

theorem resolved_pair_first_law (q : Time) (σ : Measure (C(Time,X)×C(Time,X))) :
    (σ.map (resolvedPathPair q)).map Prod.fst=σ.map Prod.fst := by
  rw [Measure.map_map measurable_fst (measurable_resolvedPathPair q)]
  rfl

theorem resolved_pair_second_law (q : Time) (σ : Measure (C(Time,X)×C(Time,X))) :
    (σ.map (resolvedPathPair q)).map Prod.snd=σ.map (resolvePathBranch q) := by
  rw [Measure.map_map measurable_snd (measurable_resolvedPathPair q)]
  rfl

end RegularPointCoordinates

end

end OAI
