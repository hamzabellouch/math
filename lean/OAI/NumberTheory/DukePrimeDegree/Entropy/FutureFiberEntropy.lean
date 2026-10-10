import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteFutureCodes

namespace OAI

/-! # Entropy conditioned on transverse coordinates and the whole future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
  [StandardBorelSpace V] [Nonempty V] [MeasurableSpace Y]

def futureFiber {M : ℕ} (T : Y → Y) (P : Y → Fin M) (F : S × V → Y)
    (z : S × V) : Set V :=
  {t | ∀ k : ℕ, P (T^[k+1] (F (z.1,t))) = P (T^[k+1] (F z))}

omit [MeasurableSpace S] [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
  [MeasurableSpace Y] in
lemma futureFiber_eq_iInter {M : ℕ} (T : Y → Y) (P : Y → Fin M)
    (F : S × V → Y) (z : S × V) :
    futureFiber T P F z =
      ⋂ n, labelFiber (fun z => finiteFutureCode T P n (F z)) z := by
  ext t
  simp only [futureFiber,labelFiber,mem_iInter,mem_ofPred_eq]
  exact (all_finiteFutureCode_eq_iff T P (F (z.1,t)) (F z)).symm

theorem conditionalEntropy_futureFiber
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {M : ℕ} {T : Y → Y} (hT : Measurable T) {P : Y → Fin M} (hP : Measurable P)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (futureFiber T P F z) ≠ 0) :
    conditionalSigmaEntropy ρ (P ∘ F)
      (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) =
      ∫ z, observationEntropy
        ((anchorNormalize (ρ.condKernel z.1) (futureFiber T P F z)).restrict
          (futureFiber T P F z)) (fun t => P (F (z.1,t))) ∂ρ := by
  simpa only [futureFiber_eq_iInter,Function.comp_def] using
    conditionalEntropy_infinite_label_restriction ρ (hP.comp hF)
      (fun n z => finiteFutureCode T P n (F z))
      (fun n => (finiteFutureCode_measurable hT hP n).comp hF)
      (transverse_finiteFutureCode_monotone T P F)
      (finiteFutureCode_fibers_antitone T P F)
      (by simpa only [futureFiber_eq_iInter] using hpos)

end DukePrimeDegree

end

end OAI
