import OAI.Geometry.RCD.Transport.PathAgreement

namespace OAI

/-! # The last meeting of two paths before a fixed time

The last meeting time is measurable. After it, the paths remain distinct up
to the fixed time. Adding time zero makes the definition total; on pairs
with a common initial point it is an actual meeting time.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def pathMeetingTimes (q : Time) (z : C(Time,X)×C(Time,X)) : Set Time :=
  {t | t=0 ∨ t≤q ∧ z.1 t=z.2 t}

def lastPathAgreement (q : Time) (z : C(Time,X)×C(Time,X)) : Time :=
  sSup (pathMeetingTimes q z)

theorem lastPathAgreement_isGreatest (q : Time) (z : C(Time,X)×C(Time,X)) :
    IsGreatest (pathMeetingTimes q z) (lastPathAgreement q z) := by
  have hc : IsClosed (pathMeetingTimes q z) :=
    isClosed_singleton.union (isClosed_Iic.inter (isClosed_eq z.1.continuous z.2.continuous))
  exact hc.isCompact.isGreatest_sSup ⟨0,Or.inl rfl⟩

theorem lastPathAgreement_le (q : Time) (z : C(Time,X)×C(Time,X)) :
    lastPathAgreement q z≤q := by
  have h := (lastPathAgreement_isGreatest q z).1
  rcases h with h | h
  · rw [h]
    exact q.property.1
  · exact h.1

theorem lastPathAgreement_eq (q : Time) {z : C(Time,X)×C(Time,X)} (hz : z.1 0=z.2 0) :
    z.1 (lastPathAgreement q z)=z.2 (lastPathAgreement q z) := by
  rcases (lastPathAgreement_isGreatest q z).1 with h | h
  · rw [h]
    exact hz
  · exact h.2

theorem ne_after_lastPathAgreement (q : Time) (z : C(Time,X)×C(Time,X))
    {t : Time} (ht : lastPathAgreement q z<t) (htq : t≤q) : z.1 t≠z.2 t := by
  intro he
  exact (not_le_of_gt ht) ((lastPathAgreement_isGreatest q z).2 (Or.inr ⟨htq,he⟩))

variable [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem measurable_lastPathAgreement (q : Time) : Measurable (lastPathAgreement (X:=X) q) := by
  apply measurable_of_Ici
  intro r
  let T : Set ((C(Time,X)×C(Time,X))×Time) :=
    {zt | r≤zt.2 ∧ (zt.2=0 ∨ zt.2≤q ∧ zt.1.1 zt.2=zt.1.2 zt.2)}
  have hT : IsClosed T := by
    apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
    apply IsClosed.union (isClosed_eq continuous_snd continuous_const)
    apply IsClosed.inter (isClosed_le continuous_snd continuous_const)
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have he : (lastPathAgreement (X:=X) q) ⁻¹' Ici r=Prod.fst '' T := by
    ext z
    constructor
    · intro hz
      exact ⟨(z,lastPathAgreement q z),⟨hz,(lastPathAgreement_isGreatest q z).1⟩,rfl⟩
    · rintro ⟨⟨w,t⟩,⟨hrt,ht⟩,rfl⟩
      exact hrt.trans ((lastPathAgreement_isGreatest q w).2 ht)
  rw [he]
  exact (isClosedMap_fst_of_compactSpace T hT).measurableSet

end RegularPointCoordinates

end

end OAI
