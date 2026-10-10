import OAI.Geometry.RCD.Transport.MeetingSpliceGeometry
import OAI.Geometry.RCD.Transport.ResolvedBranchMeasure

namespace OAI

/-! # A measurable total splice at a prescribed meeting time -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def meetingSplice (t : Time) (z : C(Time,X)×C(Time,X)) : C(Time,X) := by
  classical
  exact if h : z.1 t=z.2 t then splicePathAt t z.1 z.2 h else z.1

theorem meetingSplice_apply (t : Time) (z : C(Time,X)×C(Time,X))
    (hz : z.1 t=z.2 t) (r : Time) :
    meetingSplice t z r=if r ≤ t then z.1 r else z.2 r := by
  simp [meetingSplice,hz,splicePathAt]

theorem meetingSplice_left (t : Time) (z : C(Time,X)×C(Time,X))
    {r : Time} (hr : r ≤ t) : meetingSplice t z r=z.1 r := by
  classical
  by_cases hz : z.1 t=z.2 t <;> simp [meetingSplice,splicePathAt,hz,hr]

theorem meetingSplice_right (t : Time) (z : C(Time,X)×C(Time,X))
    (hz : z.1 t=z.2 t) {r : Time} (hr : t ≤ r) : meetingSplice t z r=z.2 r := by
  classical
  simp only [meetingSplice,dite_eq_left hz]
  exact splicePathAt_right _ _ _ _ hr

theorem meetingSplice_choice (t : Time) (z : C(Time,X)×C(Time,X)) (r : Time) :
    meetingSplice t z r=z.1 r ∨ meetingSplice t z r=z.2 r := by
  by_cases hr : r ≤ t
  · exact Or.inl (meetingSplice_left t z hr)
  · by_cases hz : z.1 t=z.2 t
    · exact Or.inr (meetingSplice_right t z hz (le_of_not_ge hr))
    · simp [meetingSplice,hz]

variable [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem measurable_meetingSplice (t : Time) : Measurable (meetingSplice (X:=X) t) := by
  classical
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  have hE : MeasurableSet {z : C(Time,X)×C(Time,X) | z.1 t=z.2 t} :=
    measurableSet_eq_fun ((measurable_path_eval t).comp measurable_fst)
      ((measurable_path_eval t).comp measurable_snd)
  have hinner : Measurable (fun z : C(Time,X)×C(Time,X) => if r ≤ t then z.1 r else z.2 r) := by
    split_ifs
    · exact (measurable_path_eval r).comp measurable_fst
    · exact (measurable_path_eval r).comp measurable_snd
  have h : Measurable (fun z : C(Time,X)×C(Time,X) =>
      if z.1 t=z.2 t then (if r ≤ t then z.1 r else z.2 r) else z.1 r) :=
    Measurable.ite hE hinner ((measurable_path_eval r).comp measurable_fst)
  convert h using 1
  funext z
  by_cases hz : z.1 t=z.2 t <;> simp [meetingSplice,splicePathAt,hz]

theorem meetingSplice_compression (t r : Time) (σ : Measure (C(Time,X)×C(Time,X))) :
    (σ.map (meetingSplice t)).map (fun γ => γ r) ≤
      (σ.map Prod.fst).map (fun γ => γ r)+(σ.map Prod.snd).map (fun γ => γ r) := by
  rw [Measure.map_map (measurable_path_eval r) (measurable_meetingSplice t),
    Measure.map_map (measurable_path_eval r) measurable_fst,
    Measure.map_map (measurable_path_eval r) measurable_snd]
  exact map_le_add_of_choice σ ((measurable_path_eval r).comp measurable_fst)
    ((measurable_path_eval r).comp measurable_snd) ((measurable_path_eval r).comp (measurable_meetingSplice t))
    (fun z => meetingSplice_choice t z r)

end RegularPointCoordinates

end

end OAI
