import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureCodes
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureSigmaAlgebra

namespace OAI

/-! # The exact sigma algebra of the countable future codes -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem countableFutureCode_sigma_generate {Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) :
    (⨆ m, observationSigma (countableFutureCode T Q m)) =
      ⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y)) := by
  apply le_antisymm
  · let : MeasurableSpace Y := ⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))
    apply iSup_le
    intro m
    have hQ (k : ℕ) : Measurable (fun y => Q (T^[k+1] y)) :=
      (comap_measurable (fun y => Q (T^[k+1] y))).iSup' k
    have hc : Measurable (countableFutureCode T Q m) := by
      apply (measurable_of_finite (Fintype.equivFin (Fin m → Fin (m+1)))).comp
      exact measurable_pi_iff.mpr fun i =>
        (heightClip_measurable (measurable_id : Measurable (id : ℕ → ℕ)) m).comp (hQ i.val)
    exact hc.comap_le
  · let : MeasurableSpace Y := ⨆ m, observationSigma (countableFutureCode T Q m)
    apply iSup_le
    intro k
    have hQ : Measurable (fun y => Q (T^[k+1] y)) := by
      apply measurable_to_countable'
      intro a
      let m := max (k+1) (a+1)
      have hk : k < m := by dsimp only [m]; omega
      have ha : a < m := by dsimp only [m]; omega
      let f : Fin (Fintype.card (Fin m → Fin (m+1))) → ℕ :=
        fun v => ((Fintype.equivFin (Fin m → Fin (m+1))).symm v ⟨k,hk⟩).val
      have hc : Measurable (countableFutureCode T Q m) :=
        (comap_measurable (countableFutureCode T Q m)).iSup' m
      have he : {y | Q (T^[k+1] y)=a} = {y | f (countableFutureCode T Q m y)=a} := by
        ext y
        simp only [f,countableFutureCode,Equiv.symm_apply_apply]
        change Q (T^[k+1] y)=a ↔ min (Q (T^[k+1] y)) m=a
        omega
      change MeasurableSet {y | Q (T^[k+1] y)=a}
      rw [he]
      exact measurableSet_eq_fun ((measurable_of_finite f).comp hc) measurable_const
    exact hQ.comap_le

theorem transverseCountableFutureSigma_eq_sup {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) :
    (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
        MeasurableSpace.comap F (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) := by
  simp_rw [transverseLabelSigma_eq_sup,
    show (fun z => countableFutureCode T Q _ (F z)) = countableFutureCode T Q _ ∘ F from rfl,
    observationSigma_comp_eq_comap]
  rw [iSup_sup_eq,iSup_const,←MeasurableSpace.comap_iSup,countableFutureCode_sigma_generate]

end DukePrimeDegree

end

end OAI
