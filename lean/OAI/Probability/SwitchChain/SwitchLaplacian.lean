import OAI.Probability.SwitchChain.ProposalUniqueness
import OAI.Probability.SwitchChain.KernelNormalization

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace Problem315

def switchLaplacian (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  ∑ H ∈ allGraphStates n d, if SwitchStep n d G H then f G - f H else 0

theorem switchStep_ne {n : Nat} {d : Fin n → Nat} {G H : GraphState n d}
    (h : SwitchStep n d G H) : G ≠ H := by
  obtain ⟨p, hp, heq⟩ := h
  intro heq'
  subst H
  exact proposalResult_ne_of_validSwitch hp heq

theorem switchKernel_mul_sub_eq {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G H : GraphState n d) :
    switchKernel n d G H * (f G - f H) =
      (if SwitchStep n d G H then f G - f H else 0) /
        (12 * (Nat.choose n 4 : ℝ)) := by
  by_cases h : G = H
  · subst H
    simp
  · rw [switchKernel_of_ne h]
    split_ifs <;> ring

theorem sub_markovApply_eq_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    f G - markovApply n d f G =
      switchLaplacian n d f G / (12 * (Nat.choose n 4 : ℝ)) := by
  calc
    f G - markovApply n d f G =
        (∑ H ∈ allGraphStates n d, switchKernel n d G H) * f G -
          ∑ H ∈ allGraphStates n d, switchKernel n d G H * f H := by
            rw [hrow G, one_mul]
            rfl
    _ = ∑ H ∈ allGraphStates n d, switchKernel n d G H * (f G - f H) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro H hH
      ring
    _ = switchLaplacian n d f G / (12 * (Nat.choose n 4 : ℝ)) := by
      simp only [switchKernel_mul_sub_eq, switchLaplacian, Finset.sum_div]

theorem dirichletEnergy_eq_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (f : GraphState n d → ℝ) :
    dirichletEnergy n d f =
      uniformInner n d f (switchLaplacian n d f) /
        (12 * (Nat.choose n 4 : ℝ)) := by
  unfold dirichletEnergy uniformInner uniformAverage
  simp only [sub_markovApply_eq_switchLaplacian hrow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  ring

theorem hasSpectralGapAtLeast_of_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n)
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (hpoincare : ∀ f : GraphState n d → ℝ,
      uniformVariance n d f ≤
        2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f)) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) := by
  intro f
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < Nat.choose n 4 := by exact_mod_cast Nat.choose_pos hn
  have hd : (0 : ℝ) < 12 * (Nat.choose n 4 : ℝ) := by positivity
  have hden : (0 : ℝ) < 24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ) := by positivity
  rw [dirichletEnergy_eq_switchLaplacian hrow]
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_div_iff₀ hden hd).mpr
  have h := mul_le_mul_of_nonneg_right (hpoincare f) (le_of_lt hd)
  nlinarith only [h]

theorem switch_chain_gap_of_laplacian_poincare {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n)
    (hpoincare : ∀ f : GraphState n d → ℝ,
      uniformVariance n d f ≤
        2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f)) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) :=
  hasSpectralGapAtLeast_of_switchLaplacian hn (switchKernel_row_sum hn) hpoincare

end Problem315

end

end OAI
