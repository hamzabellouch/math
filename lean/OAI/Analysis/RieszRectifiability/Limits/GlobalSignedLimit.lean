import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OpenOverlapCutoff
import OAI.Analysis.RieszRectifiability.Limits.GlueLocalLimits

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_global_signed_limit_of_local_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (s : ℕ → Set (Ambient d)) (hs : ∀ H, IsOpen (s H)) (hcover : ∀ x, ∃ H, x ∈ s H)
    (v : ∀ H, Lp ℝ 2 (ν.restrict (s H))) (w : ℕ → Ambient d → ℝ)
    (hmoment : ∀ H (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict (s H)) atTop
        (𝓝 (∫ x, v H x * ψ x ∂ν.restrict (s H)))) :
    ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, f =ᵐ[ν.restrict (s H)] v H ∧ MemLp f 2 (ν.restrict (s H))) ∧
      ∀ H (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict (s H)) atTop
          (𝓝 (∫ x, f x * ψ x ∂ν.restrict (s H))) := by
  have hcompat : ∀ H K, (fun x => v H x) =ᵐ[ν.restrict (s H ∩ s K)] (fun x => v K x) := by
    intro H K
    exact local_L2_agreement_on_open_overlap μ ν (s H) (s K) (hs H) (hs K)
      (v H) (v K) (Lp.memLp (v H)) (Lp.memLp (v K)) w (hmoment H) (hmoment K)
  obtain ⟨f, hfm, hf⟩ := exists_measurable_glue_of_local_L2 ν s (fun H => (hs H).measurableSet)
    hcover (fun H x => v H x) (fun H => (Lp.stronglyMeasurable (v H)).measurable)
    (fun H => Lp.memLp (v H)) hcompat
  refine ⟨f, hfm, hf, ?_⟩
  intro H ψ K B hc hLip hB
  have heq : (∫ x, f x * ψ x ∂ν.restrict (s H)) = ∫ x, v H x * ψ x ∂ν.restrict (s H) := by
    apply integral_congr_ae
    filter_upwards [(hf H).1] with x hx
    rw [hx]
  rw [heq]
  exact hmoment H ψ K B hc hLip hB

end

end RieszRectifiability

end OAI
