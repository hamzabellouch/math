import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteLabelProbability

namespace OAI

/-! # Future conditional probabilities as actual leaf mass ratios -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalProbability_futureFiber
    {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
    [StandardBorelSpace V] [Nonempty V] [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {M : ℕ} {T : Y → Y} (hT : Measurable T) {P : Y → Fin M} (hP : Measurable P)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (futureFiber T P F z) ≠ 0) (a : Fin M) :
    ρ[({z | P (F z)=a}.indicator (fun _ => (1:ℝ))) |
      ⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))] =ᵐ[ρ]
      fun z => (ρ.condKernel z.1).real ({t | P (F (z.1,t))=a} ∩ futureFiber T P F z) /
        (ρ.condKernel z.1).real (futureFiber T P F z) := by
  have H := condExp_infinite_label_probability ρ (hP.comp hF)
    (fun n z => finiteFutureCode T P n (F z))
    (fun n => (finiteFutureCode_measurable hT hP n).comp hF)
    (transverse_finiteFutureCode_monotone T P F)
    (finiteFutureCode_fibers_antitone T P F)
    (by simpa only [futureFiber_eq_iInter] using hpos) a
  filter_upwards [H] with z hz
  simp only [←futureFiber_eq_iInter,Function.comp_def] at hz
  exact hz.trans (normalized_restriction_real (ρ.condKernel z.1) (futureFiber T P F z)
    {t | P (F (z.1,t))=a}
    ((hP.comp (hF.comp measurable_prodMk_left)) (measurableSet_singleton a)))

end DukePrimeDegree

end

end OAI
