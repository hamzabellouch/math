import OAI.Analysis.CircleDomains.Topology.CountablePathTimes
import OAI.Analysis.CircleDomains.Probability.DyadicMeasurePartition

namespace OAI

/-! Atomless time measures add over all closed collar cells; the accumulating
endpoint has zero measure. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem collarCells_union : (⋃ n, collarCell n) = Ioi (⊥ : PathTime) := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact (collarTime_pos (n + 1)).trans_le hn.1
  · intro ht
    obtain ⟨n, hl, hr⟩ := exists_collarTime_cell ht
    exact mem_iUnion.mpr ⟨n, hl.le, hr⟩

theorem collarCells_aeDisjoint (μ : Measure PathTime) [NullSingletonClass μ] :
    Pairwise (AEDisjoint μ on collarCell) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij.symm)).symm
  change μ (collarCell i ∩ collarCell j) = 0
  apply measure_mono_null (t := {collarTime (i + 1)}) _ (measure_singleton _)
  intro t ht
  apply mem_singleton_iff.mpr
  exact le_antisymm (ht.2.2.trans
    (collarTime_strictAnti.antitone (Nat.succ_le_of_lt hlt))) ht.1.1

theorem sum_collar_restrict (μ : Measure PathTime) [NullSingletonClass μ] :
    Measure.sum (fun n => μ.restrict (collarCell n)) = μ := by
  rw [← Measure.restrict_iUnion_ae (collarCells_aeDisjoint μ)
    (fun _ => measurableSet_Icc.nullMeasurableSet), collarCells_union]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  have he : (Ioi (⊥ : PathTime))ᶜ = {⊥} := by
    ext t
    simp only [mem_compl_iff, mem_Ioi, not_lt, le_bot_iff, mem_singleton_iff]
  change μ (Ioi (⊥ : PathTime))ᶜ = 0
  rw [he, measure_singleton]

end CircleDomainRigidity

end

end OAI
