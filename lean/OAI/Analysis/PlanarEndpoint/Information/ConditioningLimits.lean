import OAI.Analysis.PlanarEndpoint.Information.Conditioning
import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.Sampling
import OAI.Analysis.PlanarEndpoint.Information.WeakLimits

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S Ω V W Y : Type*} [Fintype S] [Fintype V] [Fintype W] [Fintype Y]
  [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

lemma finiteInformationLaw_conditioning_tail (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (ha1 : ∑ s, a s = 1) (v : S → V) (u : S → W) (y : S → Y)
    {L η : ℝ} (hL : 1 < L) (X : S → Ω) {d : Ω → ℝ} (hd : Continuous d)
    (hrep : ∀ s, d (X s) = sampledInformation L a v y s -
      sampledInformation L a (fun s => (v s, u s)) y s) :
    (finiteInformationLaw a ha ha1 X : Measure Ω) {x | d x < -η} ≤
      ENNReal.ofReal (L ^ (-η)) := by
  rw [finiteInformationLaw_apply a ha ha1 X _
    (isOpen_lt hd continuous_const).measurableSet]
  apply ENNReal.ofReal_le_ofReal
  change (∑ s, if d (X s) < -η then a s else 0) ≤ _
  simp_rw [hrep]
  exact sampled_conditioning_exception_le a ha ha1 v u y hL

section Varying
variable [HasOuterApproxClosed Ω]
variable {S' V' W' Y' : ℕ → Type*} [∀ n, Fintype (S' n)]
  [∀ n, Fintype (V' n)] [∀ n, Fintype (W' n)] [∀ n, Fintype (Y' n)]
  (L : ℕ → ℝ) (a : (n : ℕ) → S' n → ℝ)
  (ha : ∀ n s, 0 ≤ a n s) (ha1 : ∀ n, ∑ s, a n s = 1)
  (v : (n : ℕ) → S' n → V' n) (u : (n : ℕ) → S' n → W' n)
  (y : (n : ℕ) → S' n → Y' n) (X : (n : ℕ) → S' n → Ω)

lemma ae_conditioning_in_limit {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto (fun n => finiteInformationLaw (a n) (ha n) (ha1 n) (X n))
      atTop (𝓝 μ)) (hL : ∀ n, 1 < L n) (hLlim : Tendsto L atTop atTop)
    {d : Ω → ℝ} (hd : Continuous d)
    (hrep : ∀ n s, d (X n s) = sampledInformation (L n) (a n) (v n) (y n) s -
      sampledInformation (L n) (a n) (fun s => (v n s, u n s)) (y n) s) :
    ∀ᵐ x ∂(μ : Measure Ω), 0 ≤ d x := by
  apply ae_nonneg_of_weak_limit_tails hμ hd
  intro η hη
  have henv : Tendsto (fun n => ENNReal.ofReal ((L n) ^ (-η))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.tendsto_ofReal ((tendsto_rpow_neg_atTop hη).comp hLlim)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henv
    (Eventually.of_forall (fun _ => bot_le))
    (Eventually.of_forall (fun n => finiteInformationLaw_conditioning_tail
      (a n) (ha n) (ha1 n) (v n) (u n) (y n) (hL n) (X n) hd (hrep n)))

end Varying
end PlanarEndpoint.TransverseInformation
end

end OAI
