import OAI.NumberTheory.JointDickman.Counting.PositiveBlockEnergy

namespace OAI

/-! # A nonzero bin-label correlation forces positive finite block energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem nonzero_binLabel_correlation_along_forces_blocks
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J₁ : ℕ) (hJ₁ : 0 < J₁) (k₁ : ι → ℕ) (hk₁ : ∀ i, 1 ≤ k₁ i)
    (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    (J₂ : ℕ) (hJ₂ : 0 < J₂) (k₂ : κ → ℕ) (hk₂ : ∀ i, 1 ≤ k₂ i)
    (z₂ : κ → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1) (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J₁ k₁ z₁ (r N) n) * (movingBinLabel J₂ k₂ z₂ (r N) (n+1)-μ)) /
        (r N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ (e : ℝ) (A : ℕ), 0 < e ∧ 0 < A ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → τ ≤ samplingTau →
        ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
          ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
            e ≤ arithmeticBlockAverage B L τ C (amplificationMultiplier B) (r (s N))
              (amplificationMultiplier B/A) (A*amplificationMultiplier B)
              (fun n => movingBinLabel J₂ k₂ z₂ (r (s N)) n-μ) := by
  obtain ⟨s,hs,e,he,hgraph⟩ := nonzero_binLabel_correlation_along_forces_graph
    hFord hSD hM hMP J₁ hJ₁ k₁ hk₁ z₁ hz₁ J₂ hJ₂ k₂ hk₂ z₂ hz₂ μ hμ r hr hβ hmean
  obtain ⟨A,hA,hblocks⟩ := positive_blocks_of_graph hFord hM he
  refine ⟨s,hs,e/2,A,half_pos he,hA,?_⟩
  intro L τ hL hτ hτsmall
  obtain ⟨C₀,hC₀,hC⟩ := hgraph L τ hL hτ hτsmall
  refine ⟨C₀,hC₀,?_⟩
  intro C hCC
  exact hblocks L τ C (r ∘ s) (hr.comp hs)
    (fun N n => movingBinLabel J₂ k₂ z₂ N n-μ)
    (fun N n => norm_centered_binLabel_le_two
      (fun i => primeBin (N : ℝ) J₂ (k₂ i)) z₂ hz₂ μ hμ n) (hC C hCC)

end JointDickman

end OAI
