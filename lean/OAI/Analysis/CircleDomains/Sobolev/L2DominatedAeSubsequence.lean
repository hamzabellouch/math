import OAI.Analysis.CircleDomains.Sobolev.L2DominatingSubsequence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! Strong L² convergence has a cofinal subsequence with both a common
L² majorant and pointwise almost-everywhere convergence. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_L2_dominated_ae_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (ρ : ℕ → ℕ) (P : X → ℝ), Tendsto ρ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧
      (∀ᵐ x ∂μ, (∀ n, |f (ρ n) x| ≤ P x) ∧
        Tendsto (fun n => f (ρ n) x) atTop (𝓝 (g x))) := by
  obtain ⟨σ, P, hσ, hP, hP0, hPL, hdom⟩ := exists_L2_dominating_subsequence hf hg hlim
  have hmeasure : TendstoInMeasure μ (fun n => f (σ n)) atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hlim.comp hσ)
  obtain ⟨τ, hτ, hconv⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨σ ∘ τ, P, hσ.comp hτ.tendsto_atTop, hP, hP0, hPL, ?_⟩
  filter_upwards [hdom, hconv] with x hxd hxc
  exact ⟨fun n => hxd (τ n), hxc⟩

end CircleDomainRigidity

end

end OAI
