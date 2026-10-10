import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberEntropy

namespace OAI

/-! # The exact transverse and future conditioning sigma algebra -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma transverseLabelSigma_eq_sup {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]
    {N : ℕ} (Q : S × V → Fin N) :
    transverseLabelSigma Q =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔ observationSigma Q := by
  exact MeasurableSpace.comap_prodMk Prod.fst Q

lemma finiteFutureCode_sigma {Y : Type*} {N : ℕ}
    (T : Y → Y) (P : Y → Fin N) (n : ℕ) :
    observationSigma (finiteFutureCode T P n) = observationSigma (futureName T P n) :=
  observationSigma_comp_injective _ _ (Fintype.equivFin (Fin n → Fin N)).injective

lemma observationSigma_comp_eq_comap {Y Z α : Type*} (F : Z → Y) (P : Y → α) :
    observationSigma (P ∘ F) = MeasurableSpace.comap F (observationSigma P) := by
  rw [observationSigma,observationSigma,MeasurableSpace.comap_comp]

theorem transverseFutureSigma_eq_sup {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V] {N : ℕ}
    (T : Y → Y) (P : Y → Fin N) (F : S × V → Y) :
    (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) =
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
        MeasurableSpace.comap F (⨆ n, observationSigma (futureName T P n)) := by
  simp_rw [transverseLabelSigma_eq_sup,
    show (fun z => finiteFutureCode T P _ (F z)) = finiteFutureCode T P _ ∘ F from rfl,
    observationSigma_comp_eq_comap,finiteFutureCode_sigma]
  rw [iSup_sup_eq,iSup_const,MeasurableSpace.comap_iSup]

theorem transverse_future_entropy_le {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ] {N : ℕ}
    {T : Y → Y} (hT : Measurable T) {P : Y → Fin N} (hP : Measurable P)
    {F : S × V → Y} (hF : Measurable F) :
    conditionalSigmaEntropy ρ (P ∘ F)
        (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) ≤
      conditionalSigmaEntropy ρ (P ∘ F)
        (MeasurableSpace.comap F (⨆ n, observationSigma (futureName T P n))) := by
  apply conditionalSigmaEntropy_antitone ρ (P ∘ F)
    (fun a => (hP.comp hF) (measurableSet_singleton a))
  · rw [transverseFutureSigma_eq_sup]
    exact le_sup_right
  · apply iSup_le
    intro n
    exact (measurable_fst.prodMk ((finiteFutureCode_measurable hT hP n).comp hF)).comap_le

end DukePrimeDegree

end

end OAI
