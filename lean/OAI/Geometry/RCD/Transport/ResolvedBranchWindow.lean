import OAI.Geometry.RCD.Transport.ResolvedPairAgreement
import OAI.Geometry.RCD.Sobolev.PositiveSublevelWindow

namespace OAI

/-! # A positive family of branches inside one fixed time window -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_resolved_branch_window (σ : Measure (C(Time,X)×C(Time,X)))
    (hσ : σ univ≠0) (T q : Time) (hTq : T≤q)
    (hpast : ∀ᵐ z ∂σ, z∈pathAgreement (T:ℝ))
    (hdiff : ∀ᵐ z ∂σ, z.1 q≠z.2 q) :
    ∃ S : Time, T<S ∧ S<q ∧
      let A := {z : C(Time,X)×C(Time,X) | (lastPathAgreement q z:ℝ)<(S:ℝ)}
      MeasurableSet A ∧ (σ.restrict A) univ≠0 ∧
      ∀ᵐ z ∂σ.restrict A,
        resolvedPathPair q z∈pathAgreement (T:ℝ) ∧
        resolvedPathPair q z∉pathAgreement (S:ℝ) ∧
        ∀ r : Time, lastPathAgreement q z<r → r≤q →
          z.1 r≠resolvePathBranch q z r := by
  have hroot : ∀ᵐ z ∂σ, (lastPathAgreement q z:ℝ)<(q:ℝ) := by
    filter_upwards [hpast,hdiff] with z hz hq
    exact resolved_pair_distinct_at q z (hz 0 T.property.1) hq
  have hmass : σ {z | (lastPathAgreement q z:ℝ)<(q:ℝ)}≠0 := by
    have he : {z | (lastPathAgreement q z:ℝ)<(q:ℝ)}=ᵐ[σ] univ := by
      filter_upwards [hroot] with z hz
      simp only [mem_univ,hz]
    rwa [measure_congr he]
  obtain ⟨s,hsq,hs⟩ := exists_smaller_sublevel_nonzero σ
    (fun z => (lastPathAgreement q z:ℝ)) hmass
  have hmin : ∀ᵐ z ∂σ, (T:ℝ)≤(lastPathAgreement q z:ℝ) := by
    filter_upwards [hpast] with z hz
    exact (lastPathAgreement_isGreatest q z).2 (Or.inr ⟨hTq,hz T le_rfl⟩)
  have hTs := smaller_sublevel_above_ae_lower_bound σ hmin hs
  let S : Time := ⟨s,⟨T.property.1.trans hTs.le,hsq.le.trans q.property.2⟩⟩
  have hA : MeasurableSet {z : C(Time,X)×C(Time,X) | (lastPathAgreement q z:ℝ)<s} :=
    measurableSet_lt ((measurable_lastPathAgreement q).subtype_coe) measurable_const
  refine ⟨S,hTs,hsq,hA,?_,?_⟩
  · rwa [Measure.restrict_apply_univ]
  · filter_upwards [ae_restrict_mem hA,hpast.filter_mono Measure.restrict_le_self.absolutelyContinuous.ae_le]
      with z hz hp
    have h0 := hp 0 T.property.1
    refine ⟨resolved_branch_common_past q hTq hp,?_,?_⟩
    · intro ha
      have hle := (resolved_pair_agreement_iff q z h0 (show S≤q from hsq.le)).mp ha
      exact (not_le_of_gt hz) hle
    · exact fun r hr hrq => resolvePathBranch_ne_after q z h0 hr hrq

end RegularPointCoordinates

end

end OAI
