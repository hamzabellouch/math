import OAI.NumberTheory.JointDickman.Amplification.BinCorrelationLimit

namespace OAI

/-! # Centered bin labels at consecutive integers decorrelate -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def centeredBinCorrelation {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (k₁ : ι → ℕ) (z₁ : ι → ℂ) (J₂ : ℕ)
    (z₂ : Fin (J₂-1) → ℂ) (μ : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ range N, star (movingBinLabel J₁ k₁ z₁ N n) *
    (movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ N (n+1)-μ))/(N : ℂ)

theorem centeredBinCorrelation_norm_le_two {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (k₁ : ι → ℕ) (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    (J₂ : ℕ) (z₂ : Fin (J₂-1) → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (N : ℕ) :
    ‖centeredBinCorrelation J₁ k₁ z₁ J₂ z₂ μ N‖ ≤ 2 := by
  have hterm (n : ℕ) : ‖star (movingBinLabel J₁ k₁ z₁ N n) *
      (movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ N (n+1)-μ)‖ ≤ 2 := by
    rw [norm_mul,norm_star]
    have h₁ := norm_binLabel_le_one (fun i => primeBin (N : ℝ) J₁ (k₁ i)) z₁ hz₁ n
    have h₂ := norm_centered_binLabel_le_two (fun i : Fin (J₂-1) => primeBin (N : ℝ) J₂ (i.val+1))
      z₂ hz₂ μ hμ (n+1)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  unfold centeredBinCorrelation
  rw [norm_div,Complex.norm_natCast]
  by_cases hN : N = 0
  · simp [hN]
  have hs := norm_sum_le_of_le (range N) (fun n _ => hterm n)
  simp only [sum_const,nsmul_eq_mul,Finset.card_range] at hs
  exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < N)).mpr (by simpa only [mul_comm] using hs)

theorem centeredBinCorrelation_tendsto
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
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
  have hzero : β = 0 := bin_correlation_limit_zero hMR hMRT hKMT hFord hSD hSW hM hMP hMC
    J₁ hJ₁ k₁ hk₁ z₁ hz₁ hJ₂ z₂ hz₂ μ hμ hcenter (ns ∘ r ∘ s) (hnr.comp hs) hlim
  exact ⟨r ∘ s,by simpa only [hzero,Function.comp_def] using hlim⟩

end JointDickman

end OAI
