import OAI.Probability.SwitchChain.FiniteKernelTV
import OAI.Probability.SwitchChain.FiniteKernelAlgebra
import OAI.Probability.SwitchChain.SwitchFoundations
import OAI.Probability.SwitchChain.KernelNormalization

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem315

lemma kernelPow_eq_matrix_pow (n : ℕ) (d : Fin n → ℕ) (t : ℕ) :
    (kernelPow n d t : Matrix (GraphState n d) (GraphState n d) ℝ) =
      (Matrix.of (switchKernel n d)) ^ t := by
  classical
  induction t with
  | zero =>
      funext G H
      change (if G = H then (1 : ℝ) else 0) = (1 : Matrix (GraphState n d) (GraphState n d) ℝ) G H
      simp [Matrix.one_apply]
  | succ t ih =>
      funext G H
      change (∑ K ∈ allGraphStates n d, kernelPow n d t G K * switchKernel n d K H) = _
      rw [ih, pow_succ]
      rfl

theorem switch_tv_bound_of_gap (n : ℕ) (d : Fin n → ℕ)
    (hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1)
    {γ : ℝ} (hγ : γ ≤ 1) (hgap : hasSpectralGapAtLeast n d γ)
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤
      Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (-γ * (t : ℝ)) := by
  classical
  have : Nonempty (GraphState n d) := ⟨G⟩
  have hN : (0 : ℝ) < (Fintype.card (GraphState n d) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsymm : Matrix.IsSymm (Matrix.of (switchKernel n d)) :=
    Matrix.IsSymm.ext (fun G H => switchKernel_symm H G)
  have hpos : ∀ f : GraphState n d → ℝ,
      0 ≤ ∑ G, f G * ∑ H, switchKernel n d G H * f H :=
    FiniteKernel.lazy_inner_nonneg (switchKernel n d) hrows switchKernel_symm
      switchKernel_nonneg switchKernel_self_ge_half
  have hgap' : ∀ f : GraphState n d → ℝ, (∑ G, f G) = 0 →
      γ * (∑ G, (f G) ^ 2) ≤
        ∑ G, f G * (f G - ∑ H, switchKernel n d G H * f H) := by
    intro f hf
    have hh := hgap f
    have havg : uniformAverage n d f = 0 := by
      simp [uniformAverage, allGraphStates, hf]
    unfold uniformVariance at hh
    rw [havg] at hh
    simp only [sub_zero, uniformAverage, stateCount,
      allGraphStates, Finset.card_univ, dirichletEnergy, uniformInner, markovApply] at hh
    rw [← mul_div_assoc] at hh
    exact (div_le_div_iff_of_pos_right hN).mp hh
  have ht := Analytic.matrix_tv_bound_of_gap (Matrix.of (switchKernel n d)) hsymm hrows hγ hpos hgap' t G
  simpa only [tvDistanceFrom, allGraphStates, stateCount, Finset.card_univ,
    kernelPow_eq_matrix_pow] using ht

lemma switch_gap_parameter_le_one (n : ℕ) (hn : 4 ≤ n) :
    (1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)) ≤ 1 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose n 4 : ℝ) := by
    exact_mod_cast (Nat.choose_pos hn)
  have hd : (1 : ℝ) ≤ 24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hn')) hc
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd

theorem switch_chain_tv_bound_of_stochastic_and_gap (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1)
    (hgap : hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  have h := switch_tv_bound_of_gap n d hrows (switch_gap_parameter_le_one n hn) hgap t G
  convert h using 1
  congr 2
  ring

theorem switch_chain_tv_bound_of_spectralGap (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hgap : hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  apply switch_chain_tv_bound_of_stochastic_and_gap n d hn _ hgap t G
  intro H
  simpa only [allGraphStates] using switchKernel_row_sum hn H

end Problem315

end

end OAI
