import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberProbability
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformation

namespace OAI

/-! # Integrable information ratios for whole future fibers -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem futureFiber_information_integrable_integral
    {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
    [StandardBorelSpace V] [Nonempty V] [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {M : ℕ} [NeZero M] {T : Y → Y} (hT : Measurable T)
    {P : Y → Fin M} (hP : Measurable P) {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (futureFiber T P F z) ≠ 0) :
    let I := fun z => -Real.log
      ((ρ.condKernel z.1).real ({t | P (F (z.1,t))=P (F z)} ∩ futureFiber T P F z) /
        (ρ.condKernel z.1).real (futureFiber T P F z))
    Integrable I ρ ∧
      conditionalSigmaEntropy ρ (P ∘ F)
        (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) = ∫ z, I z ∂ρ := by
  dsimp only
  let m := ⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))
  let : MeasurableSpace (S × V) := Prod.instMeasurableSpace
  have hm : m ≤ (inferInstance : MeasurableSpace (S × V)) := by
    apply iSup_le
    intro n
    exact (measurable_fst.prodMk ((finiteFutureCode_measurable hT hP n).comp hF)).comap_le
  have H := conditionalInformation_integrable_integral m ρ (P ∘ F) (hP.comp hF) hm
  have heq : conditionalInformation ρ (P ∘ F) m =ᵐ[ρ] fun z => -Real.log
      ((ρ.condKernel z.1).real ({t | P (F (z.1,t))=P (F z)} ∩ futureFiber T P F z) /
        (ρ.condKernel z.1).real (futureFiber T P F z)) := by
    filter_upwards [ae_all_iff.mpr (fun a => conditionalProbability_futureFiber ρ hT hP hF hpos a)]
      with z hz
    exact congrArg (-Real.log ·) (hz (P (F z)))
  exact ⟨H.1.congr heq,H.2.symm.trans (integral_congr_ae heq)⟩

end DukePrimeDegree

end

end OAI
