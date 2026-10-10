import OAI.NumberTheory.JointDickman.Counting.SubsequencePositiveEnergy

namespace OAI

/-! # Positive arithmetic graph energy along a prescribed bad subsequence -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem nonzero_binLabel_correlation_along_forces_graph
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
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → τ ≤ samplingTau →
        ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
          ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
            e ≤ arithmeticOffDiagonalGraph B L τ C (amplificationMultiplier B) (r (s N))
              (fun n => movingBinLabel J₂ k₂ z₂ (r (s N)) n-μ) /
                ((B : ℝ)*amplificationMultiplier B) := by
  let H : ℕ → ℕ → ℂ := fun N n => movingBinLabel J₂ k₂ z₂ N (n+1)-μ
  have hH : ∀ N n, ‖H N n‖ ≤ 2 := fun N n =>
    norm_centered_binLabel_le_two (fun i => primeBin (N : ℝ) J₂ (k₂ i)) z₂ hz₂ μ hμ (n+1)
  obtain ⟨s,hs,e,he,hE⟩ := nonzero_binLabel_correlation_along_forces_energy
    hFord hSD hM hMP J₁ hJ₁ k₁ hk₁ z₁ hz₁ H hH r hr hβ hmean
  refine ⟨s,hs,e/2,half_pos he,?_⟩
  intro L τ hL hτ hτsmall
  obtain ⟨C₀,hC₀,hC⟩ := hE L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hCC
  have hOff := positive_offDiagonal_of_energy hFord hM hL hτ.le hτsmall C H hH (r ∘ s) (hr.comp hs) he (hC C hCC)
  filter_upwards [hOff,amplificationMultiplier_le_cutoff] with B hB hT
  have hgraph := centered_binLabel_offDiagonal_graph J₂ hJ₂ k₂ hk₂ z₂ μ B L τ C
    (amplificationMultiplier B) hT
  filter_upwards [hB,(hr.comp hs).tendsto_atTop.eventually hgraph] with N hN hGN
  simp only [Function.comp_apply] at hGN
  change e/2 ≤ firstFormOffDiagonal B L τ C (amplificationOuterWeight B)
    (amplificationInnerWeight (amplificationMultiplier B))
    (fun m => movingBinLabel J₂ k₂ z₂ (r (s N)) (m+1)-μ) (r (s N)) / _ at hN
  rwa [hGN] at hN

end JointDickman

end OAI
