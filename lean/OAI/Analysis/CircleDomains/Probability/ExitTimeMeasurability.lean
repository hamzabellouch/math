import OAI.Analysis.CircleDomains.Selection.LastEntryCuts
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI

/-! Borel first-exit and last-entry locations for the collar crossing laws. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem firstExit_notMem_of_exists (γ : C(PathTime, X)) {V : Set X}
    (hV : IsOpen V) (hex : ∃ t, γ t ∉ V) : γ (firstExitTime γ V) ∉ V :=
  (hV.isClosed_compl.preimage γ.continuous).isCompact.sInf_mem hex

theorem lt_firstExit_iff_mapsTo (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    {t : PathTime} (ht : t < ⊤) :
    t < firstExitTime γ V ↔ MapsTo γ (Iic t) V := by
  constructor
  · intro h s hs
    exact mem_before_firstExit γ V (hs.trans_lt h)
  · intro h
    by_contra hn
    have hle : firstExitTime γ V ≤ t := le_of_not_gt hn
    by_cases hex : ∃ s, γ s ∉ V
    · exact firstExit_notMem_of_exists γ hV hex (h hle)
    · have he : {s | γ s ∉ V} = ∅ := not_nonempty_iff_eq_empty.mp hex
      have htop : firstExitTime γ V = ⊤ := by rw [firstExitTime, he, sInf_empty]
      exact ht.not_ge (htop ▸ hle)

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_firstExitTime (V : Set X) (hV : IsOpen V) :
    Measurable (fun γ : C(PathTime, X) => firstExitTime γ V) := by
  apply measurable_of_Ioi
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp
  · have he : (fun γ : C(PathTime, X) => firstExitTime γ V) ⁻¹' Ioi t =
        {γ : C(PathTime, X) | MapsTo γ (Iic t) V} := by
      ext γ
      exact lt_firstExit_iff_mapsTo γ hV (lt_top_iff_ne_top.mpr ht)
    rw [he]
    exact (ContinuousMap.isOpen_setOfPred_mapsTo isClosed_Iic.isCompact hV).measurableSet

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem continuous_reversedPath : Continuous (reversedPath (X := X)) :=
  ContinuousMap.continuous_precomp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

theorem measurable_lastEntryTime (V : Set X) (hV : IsOpen V) :
    Measurable (fun γ : C(PathTime, X) => lastEntryTime γ V) :=
  unitInterval.continuous_symm.measurable.comp
    ((measurable_firstExitTime V hV).comp continuous_reversedPath.measurable)

theorem measurable_lastEntryLocation (V : Set X) (hV : IsOpen V)
    [MeasurableSpace X] [BorelSpace X] :
    Measurable (fun γ : C(PathTime, X) => γ (lastEntryTime γ V)) :=
  continuous_eval.measurable.comp (measurable_id.prodMk (measurable_lastEntryTime V hV))

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem mem_after_lastEntry (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : lastEntryTime γ V < t) : γ t ∈ V := by
  have hlt : unitInterval.symm t < firstExitTime (reversedPath γ) V :=
    unitInterval.symm_lt_comm.mpr ht
  have hm := mem_before_firstExit (reversedPath γ) V hlt
  simpa only [reversedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    unitInterval.symm_symm] using hm

end CircleDomainRigidity

end

end OAI
