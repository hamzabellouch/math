import OAI.Analysis.CircleDomains.Sobolev.HilbertWeakSubsequence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

/-! Bounded L² sequences admit subsequences whose pairings converge.
The representative integrals below are obtained from the actual L² limits. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_L2_weak_subsequence
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
    (u : ℕ → X → ℝ) (hu : ∀ n, MemLp (u n) 2 μ)
    (C : ℝ) (hbound : ∀ n, ‖(hu n).toLp (u n)‖ ≤ C) :
    ∃ V : Lp ℝ 2 μ, ‖V‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ w : Lp ℝ 2 μ,
        Tendsto (fun n => ∫ x, u (σ n) x * w x ∂μ) atTop
          (𝓝 (∫ x, V x * w x ∂μ)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 μ) := inferInstance
  obtain ⟨V, hV, σ, hσ, hlim⟩ := exists_hilbert_weak_subsequence
    (fun n => (hu n).toLp (u n)) C hbound
  refine ⟨V, hV, σ, hσ, ?_⟩
  intro w
  have he (n : ℕ) : inner ℝ ((hu n).toLp (u n)) w = ∫ x, u n x * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hu n).coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
  have hVeq : inner ℝ V w = ∫ x, V x * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [Real.inner_apply]
  simpa only [he, hVeq] using hlim w

end CircleDomainRigidity

end

end OAI
