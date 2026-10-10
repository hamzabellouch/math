import OAI.NumberTheory.JointDickman.Counting.ArithmeticBlockMean
import OAI.NumberTheory.JointDickman.Counting.SubsequencePositiveBlocks

namespace OAI

/-! # Every convergent mixed bin-label correlation has zero centered limit -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem bin_correlation_limit_zero
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
    (hcenter : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J₂ z₂ μ D) atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ}
    (hlimit : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J₁ k₁ z₁ (r N) n) *
        (movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ (r N) (n+1)-μ))/(r N : ℂ))
      atTop (𝓝 β)) : β = 0 := by
  by_contra hβ
  obtain ⟨s,hs,e,A,he,hA,hpositive⟩ := nonzero_binLabel_correlation_along_forces_blocks
    hFord hSD hM hMP J₁ hJ₁ k₁ hk₁ z₁ hz₁ J₂ hJ₂ (fun i : Fin (J₂-1) => i.val+1)
    (fun _ => by omega) z₂ hz₂ μ hμ r hr hβ hlimit
  obtain ⟨τ,hτ,_,hτsmall,hzero⟩ := arithmetic_block_centered_mean hMR hMRT hKMT hFord hSD hSW hM hMP hMC
    hJ₂ z₂ hz₂ μ hμ hcenter hA (by norm_num : 10000 ≤ (10000 : ℕ)) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨C₀,hC₀,hpos⟩ := hpositive 10000 τ (by norm_num) hτ hτsmall
  obtain ⟨C₁,hC₁,hneg⟩ := hzero (e/2) (half_pos he)
  have hp := hpos (max C₀ C₁) (le_max_left _ _)
  have hn := hneg (max C₀ C₁) (le_max_right _ _)
  have hfalse : ∀ᶠ B : ℕ in atTop, False := by
    filter_upwards [hp,hn] with B hb hsmall
    have hsmall' := (hr.comp hs).tendsto_atTop.eventually hsmall
    obtain ⟨N,hN,hNsmall⟩ := (hb.and hsmall').exists
    have hh : e ≤ |arithmeticBlockAverage B 10000 τ (max C₀ C₁) (amplificationMultiplier B)
        (r (s N)) (amplificationMultiplier B/A) (A*amplificationMultiplier B)
        (fun n => movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ (r (s N)) n-μ)| :=
      hN.trans (le_abs_self _)
    change _ < e/2 at hNsmall
    simp only [movingBinLabel,Function.comp_apply] at hh hNsmall
    linarith only [hh,hNsmall,he]
  exact hfalse.exists.elim (fun _ h => h)

end JointDickman

end OAI
