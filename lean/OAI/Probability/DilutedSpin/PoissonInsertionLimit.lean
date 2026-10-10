import OAI.Probability.DilutedSpin.AveragedEnergyRoot
import OAI.Probability.DilutedSpin.FullRootCounts

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter ConcreteReservoir
open scoped Topology BigOperators NNReal

/-- Poisson many distinct inserted labels, with their physical disorder, obey
 the same ordered full-shape limit. The linear Poisson tail is retained, not
 replaced by a bound on the number of cavity interactions. -/
lemma poissonInsertionOn_comparison_tendsto
    {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (hFm : ∀ k,Measurable (F k))
    {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hF : ∀ k x s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
    Tendsto (fun L => limsup (fun n => ∫ k,
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F k x) ∂μ k)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)|
      ∂poissonMeasure ρ) atTop) atTop (𝓝 0) := by
  apply poisson_mixture_double_limit ρ _ (B := 2*B) (C := 2*D)
  · intros; exact abs_nonneg _
  · intro k L n
    have h1 := abs_integral_le_bound (μ := μ k) (fun x =>
      reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (F k x) (hF k x))
    have h2 := abs_integral_le_bound (μ := μ k) (fun x =>
      (trialLog_continuous_bound L (FiniteLaw.spinLog (F k x))
        (FiniteLaw.spinLog_continuous (F k x))
        (FiniteLaw.spinLog_bound (F k x) (hF k x)) _
        (fun i => gridExponents_pos L i.castSucc)).2
        (reservoirTrialLaw M C H (Ns L n+1) L (us L n)))
    exact (abs_sub _ _).trans (by linarith)
  · intro k
    exact randomInsertionOn_comparison_tendsto M hα C H Ns hNs us hcontrol (μ k) (F k)
      (hFm k) (by positivity) (hF k)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
