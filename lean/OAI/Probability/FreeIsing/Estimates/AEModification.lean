import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Factors.Transport

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem isFactorOfIID_of_aemeasurable {d : ℕ} {theta : ℝ}
    (Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin))
    (hPhi : AEMeasurable Phi (labelMeasure d))
    (hLaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hEquiv : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)) :
    IsFactorOfIID d theta := by
  refine ⟨hPhi.mk Phi, hPhi.measurable_mk, ?_, ?_⟩
  · rw [← Measure.map_congr hPhi.ae_eq_mk]
    exact hLaw
  · intro g
    exact FactorTransport.ae_equivariant_congr
      (measurePreserving_relabel g).quasiMeasurePreserving
      hPhi.ae_eq_mk (hEquiv g)

theorem isFactorOfIID_iff_aemeasurable (d : ℕ) (theta : ℝ) :
    IsFactorOfIID d theta ↔
      ∃ Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin),
        AEMeasurable Phi (labelMeasure d) ∧
        HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)) ∧
        ∀ g : TreeAut d,
          ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U) := by
  constructor
  · rintro ⟨Phi, hPhi, hLaw, hEquiv⟩
    exact ⟨Phi, hPhi.aemeasurable, hLaw, hEquiv⟩
  · rintro ⟨Phi, hPhi, hLaw, hEquiv⟩
    exact isFactorOfIID_of_aemeasurable Phi hPhi hLaw hEquiv

theorem isFactorOfIID_of_coordinatewise_ae {d : ℕ} {theta : ℝ}
    (Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin))
    (hPhi : ∀ v, AEMeasurable (fun U => Phi U v) (labelMeasure d))
    (hLaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hEquiv : ∀ (g : TreeAut d) (v : TreeVertex d),
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) v = relabel g (Phi U) v) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_aemeasurable Phi (aemeasurable_pi_iff.mpr hPhi) hLaw
  intro g
  filter_upwards [ae_all_iff.mpr (hEquiv g)] with U hU
  exact funext hU

end Problem367

end

end OAI
