import OAI.Geometry.RCD.Transport.PathMeetingSplice
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

namespace OAI

/-! # A measurable splice which removes repeated meetings before a fixed time -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def resolvePathBranch (q : Time) (z : C(Time,X)×C(Time,X)) : C(Time,X) := by
  classical
  exact if h : z.1 0=z.2 0 then
    splicePathAt (lastPathAgreement q z) z.1 z.2 (lastPathAgreement_eq q h) else z.2

theorem resolvePathBranch_apply (q : Time) (z : C(Time,X)×C(Time,X))
    (hz : z.1 0=z.2 0) (s : Time) :
    resolvePathBranch q z s=if s≤lastPathAgreement q z then z.1 s else z.2 s := by
  simp [resolvePathBranch,hz,splicePathAt]

theorem resolvePathBranch_zero (q : Time) (z : C(Time,X)×C(Time,X)) :
    resolvePathBranch q z 0=z.2 0 := by
  classical
  by_cases hz : z.1 0=z.2 0
  · simp [resolvePathBranch,hz,splicePathAt_zero]
  · simp [resolvePathBranch,hz]

theorem resolvePathBranch_one (q : Time) (z : C(Time,X)×C(Time,X)) :
    resolvePathBranch q z 1=z.2 1 := by
  classical
  by_cases hz : z.1 0=z.2 0 <;> simp [resolvePathBranch,hz,splicePathAt_one]

theorem resolvePathBranch_choice (q : Time) (z : C(Time,X)×C(Time,X)) (s : Time) :
    resolvePathBranch q z s=z.1 s ∨ resolvePathBranch q z s=z.2 s := by
  classical
  by_cases hz : z.1 0=z.2 0
  · rw [resolvePathBranch_apply q z hz]
    split_ifs <;> simp
  · simp [resolvePathBranch,hz]

theorem resolvePathBranch_ne_after (q : Time) (z : C(Time,X)×C(Time,X))
    (hz : z.1 0=z.2 0) {s : Time} (hs : lastPathAgreement q z<s) (hsq : s≤q) :
    z.1 s≠resolvePathBranch q z s := by
  rw [resolvePathBranch_apply q z hz,ite_eq_right (not_le.mpr hs)]
  exact ne_after_lastPathAgreement q z hs hsq

theorem resolvePathBranch_isGeodesic (q : Time) (z : C(Time,X)×C(Time,X))
    (hγ : IsGeodesic z.1) (hζ : IsGeodesic z.2) :
    IsGeodesic (resolvePathBranch q z) := by
  classical
  by_cases hz : z.1 0=z.2 0
  · simp only [resolvePathBranch,dite_eq_left hz]
    by_cases ht : 0<(lastPathAgreement q z:ℝ)
    · exact splicePathAt_isGeodesic _ _ _ _ hγ hζ hz
        (geodesic_length_eq_of_meeting hγ hζ hz ht (lastPathAgreement_eq q hz))
    · have ht0 : lastPathAgreement q z=0 :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) (lastPathAgreement q z).property.1)
      have he : splicePathAt (lastPathAgreement q z) z.1 z.2 (lastPathAgreement_eq q hz)=z.2 := by
        ext s
        exact splicePathAt_right _ _ _ _ (by rw [ht0]; exact s.property.1)
      rw [he]
      exact hζ
  · simpa only [resolvePathBranch,dite_eq_right hz] using hζ

variable [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem measurable_resolvePathBranch (q : Time) : Measurable (resolvePathBranch (X:=X) q) := by
  classical
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  have h0 : MeasurableSet {z : C(Time,X)×C(Time,X) | z.1 0=z.2 0} :=
    measurableSet_eq_fun ((measurable_path_eval 0).comp measurable_fst)
      ((measurable_path_eval 0).comp measurable_snd)
  have hs : MeasurableSet {z : C(Time,X)×C(Time,X) | s≤lastPathAgreement q z} :=
    measurableSet_le measurable_const (measurable_lastPathAgreement q)
  have hi : Measurable (fun z : C(Time,X)×C(Time,X) =>
      if s≤lastPathAgreement q z then z.1 s else z.2 s) :=
    Measurable.ite hs ((measurable_path_eval s).comp measurable_fst)
      ((measurable_path_eval s).comp measurable_snd)
  have h : Measurable (fun z : C(Time,X)×C(Time,X) =>
      if z.1 0=z.2 0 then (if s≤lastPathAgreement q z then z.1 s else z.2 s) else z.2 s) :=
    Measurable.ite h0 hi ((measurable_path_eval s).comp measurable_snd)
  convert h using 1
  funext z
  by_cases hz : z.1 0=z.2 0 <;> simp [resolvePathBranch,splicePathAt,hz]

end RegularPointCoordinates

end

end OAI
