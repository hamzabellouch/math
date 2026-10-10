import OAI.NumberTheory.JointDickman.Amplification.BinDecorrelation
import OAI.NumberTheory.JointDickman.Amplification.BinCorrelationLimitDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem centeredBinCorrelation_tendsto_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (hJ₁ : 0 < J₁) (k₁ : ι → ℕ) (hk₁ : ∀ i, 1 ≤ k₁ i)
    (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    {J₂ : ℕ} (hJ₂ : 0 < J₂) (z₂ : Fin (J₂-1) → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hcenter : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J₂ z₂ μ D) atTop (𝓝 0)) :
    Tendsto (centeredBinCorrelation J₁ k₁ z₁ J₂ z₂ μ) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨r,hr,hnr⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hbound (n : ℕ) : centeredBinCorrelation J₁ k₁ z₁ J₂ z₂ μ (ns (r n)) ∈
      Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact centeredBinCorrelation_norm_le_two J₁ k₁ z₁ hz₁ J₂ z₂ hz₂ μ hμ _
  obtain ⟨β,_,s,hs,hlim⟩ := (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq hbound
  have hzero : β = 0 := bin_correlation_limit_zero_proved hKMT hFord hSD hSW hM hMP hMC
    J₁ hJ₁ k₁ hk₁ z₁ hz₁ hJ₂ z₂ hz₂ μ hμ hcenter (ns ∘ r ∘ s) (hnr.comp hs) hlim
  exact ⟨r ∘ s,by simpa only [hzero,Function.comp_def] using hlim⟩

end JointDickman

end OAI
