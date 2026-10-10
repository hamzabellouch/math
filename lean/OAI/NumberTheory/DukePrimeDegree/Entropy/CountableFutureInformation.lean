import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureSigma
import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteLabelProbability
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformation

namespace OAI

/-! # Information of finite labels given the countable future

Conditional probabilities are actual leaf mass ratios, and their
logarithms are integrable for each finite present observation.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
  [StandardBorelSpace V] [Nonempty V] [MeasurableSpace Y]

theorem conditionalProbability_countableFutureFiber
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {M : ℕ} {P : Y → Fin M} (hP : Measurable P)
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0) (a : Fin M) :
    ρ[({z | P (F z)=a}.indicator (fun _ => (1:ℝ))) |
      ⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))] =ᵐ[ρ]
      fun z => (ρ.condKernel z.1).real ({t | P (F (z.1,t))=a} ∩ countableFutureFiber T Q F z) /
        (ρ.condKernel z.1).real (countableFutureFiber T Q F z) := by
  have H := condExp_infinite_label_probability ρ (hP.comp hF)
    (fun m z => countableFutureCode T Q m (F z))
    (fun m => (countableFutureCode_measurable hT hQ m).comp hF)
    (transverse_countableFutureCode_monotone T Q F)
    (countableFutureCode_fibers_antitone T Q F)
    (by simpa only [countableFutureFiber_eq_iInter] using hpos) a
  filter_upwards [H] with z hz
  simp only [←countableFutureFiber_eq_iInter,Function.comp_def] at hz
  exact hz.trans (normalized_restriction_real (ρ.condKernel z.1) (countableFutureFiber T Q F z)
    {t | P (F (z.1,t))=a}
    ((hP.comp (hF.comp measurable_prodMk_left)) (measurableSet_singleton a)))

theorem countableFutureFiber_information_integrable_integral
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {M : ℕ} [NeZero M] {P : Y → Fin M} (hP : Measurable P)
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0) :
    let I := fun z => -Real.log
      ((ρ.condKernel z.1).real ({t | P (F (z.1,t))=P (F z)} ∩ countableFutureFiber T Q F z) /
        (ρ.condKernel z.1).real (countableFutureFiber T Q F z))
    Integrable I ρ ∧
      conditionalSigmaEntropy ρ (P ∘ F)
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
          MeasurableSpace.comap F (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y)))) =
        ∫ z, I z ∂ρ := by
  dsimp only
  rw [←transverseCountableFutureSigma_eq_sup T Q F]
  let m := ⨆ n, transverseLabelSigma (fun z => countableFutureCode T Q n (F z))
  let : MeasurableSpace (S × V) := Prod.instMeasurableSpace
  have hm : m ≤ (inferInstance : MeasurableSpace (S × V)) := by
    apply iSup_le
    intro n
    exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ n).comp hF)).comap_le
  have H := conditionalInformation_integrable_integral m ρ (P ∘ F) (hP.comp hF) hm
  have heq : conditionalInformation ρ (P ∘ F) m =ᵐ[ρ] fun z => -Real.log
      ((ρ.condKernel z.1).real ({t | P (F (z.1,t))=P (F z)} ∩ countableFutureFiber T Q F z) /
        (ρ.condKernel z.1).real (countableFutureFiber T Q F z)) := by
    filter_upwards [ae_all_iff.mpr (fun a =>
      conditionalProbability_countableFutureFiber ρ hP hQ hT hF hpos a)] with z hz
    exact congrArg (-Real.log ·) (hz (P (F z)))
  exact ⟨H.1.congr heq,H.2.symm.trans (integral_congr_ae heq)⟩

end DukePrimeDegree

end

end OAI
