import OAI.Probability.DilutedSpin.CountedSpinMean

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory

lemma measurePreserving_rootArray_coordinate {X : Type} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun z : RootPath X n => rootArray n z i) (rootLaw n μ) (μ i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact measurePreserving_fst
    | succ i =>
      exact (ih (fun j => μ j.succ) i).comp (measurePreserving_snd)

lemma rootLaw_ae_all {X : Type} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (P : Fin n → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ i, P i x) :
    ∀ᵐ z ∂rootLaw n μ, ∀ i, P i (rootArray n z i) := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_rootArray_coordinate n μ i).quasiMeasurePreserving.ae (hP i)

namespace SizeCoupling
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

omit [Countable I] [MeasurableSingletonClass I] in
lemma countedMean_congr (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta theta' : X → InteractionSample p) (field field' : Y → ℝ)
    (hθ : theta =ᵐ[μ] theta') (hh : field =ᵐ[ξ] field')
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (k l : ℕ) :
    countedMean (N := N) μ ξ ν theta field Q m ψ k l =
      countedMean (N := N) μ ξ ν theta' field' Q m ψ k l := by
  unfold countedMean
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [rootLaw_ae_all k (fun _ => μ) (fun _ x => theta x = theta' x) (fun _ => hθ)] with x hx
  apply integral_congr_ae
  filter_upwards [rootLaw_ae_all N (fun _ => ξ) (fun _ y => field y = field' y) (fun _ => hh)] with y hy
  congr 1
  · funext i; exact hx i
  · funext i; exact hy i

end SizeCoupling
end DilutedSpinGlass
end

end

end OAI
