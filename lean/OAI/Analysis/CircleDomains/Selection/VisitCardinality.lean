import OAI.Analysis.CircleDomains.Selection.VisitCounts

namespace OAI

/-! The measurable finite-witness count agrees with the actual extended sum
of unit tolls over all visit times. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem visitCount_eq_tsum (γ : C(PathTime, X)) (x : X) :
    visitCount γ x = ∑' t : PathTime, if γ t = x then (1 : ℝ≥0∞) else 0 := by
  classical
  apply le_antisymm
  · unfold visitCount
    apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, heq⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if γ (t i) = x then (1 : ℝ≥0∞) else 0 := by
          simp only [heq, ite_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ ∑' t : PathTime, if γ t = x then (1 : ℝ≥0∞) else 0 :=
          ENNReal.tsum_comp_le_tsum_of_injective ht (fun t => if γ t = x then 1 else 0)
    · exact bot_le
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun t => γ t = x)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have ht : (γ, x) ∈ visitAtLeastSet (Fintype.card E) := by
      refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
      intro i
      exact (Finset.mem_filter.mp (e i).property).2
    have hb := visitCount_ge_nat ht
    simpa only [Finset.sum_boole, Fintype.card_coe] using hb

end CircleDomainRigidity

end

end OAI
