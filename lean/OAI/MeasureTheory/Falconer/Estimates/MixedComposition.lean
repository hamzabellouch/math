import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! # Pointwise mixed derivative budgets for composition

The fixed constant is the actual finite sum over ordered partitions. A
derivative budget of degree `i` for the inner map gives degree `n` for its
composition, with no loss depending on the scale.
-/

namespace Falconer
open Set
open scoped ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compact_iteratedFDeriv_bound {f : E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  choose A hA using fun i : ℕ => hK.exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (by simp : (i : ℕ∞ω) ≤ ∞)).continuousOn)
  let C := ∑ i ∈ Finset.range (n+1), max 0 (A i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro i hi x hx
  apply (hA i x hx).trans
  apply (le_max_right 0 (A i)).trans
  exact Finset.single_le_sum (fun j _ => le_max_left 0 (A j)) (by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

noncomputable def mixedCompositionBudget (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ j, B (c.partSize j)

theorem mixedCompositionBudget_nonneg {B : ℕ → ℝ} (hB : ∀ i, 0 ≤ B i) (n : ℕ) :
    0 ≤ mixedCompositionBudget B n := by
  exact Finset.sum_nonneg (fun c _ => Finset.prod_nonneg (fun j _ => hB _))

theorem mixed_composition_derivative_bound {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    {B : ℕ → ℝ} {C D : ℝ} (hC : 0 ≤ C)
    (n : ℕ)
    (houter : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hinner : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B i*D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ mixedCompositionBudget B n*C*D^n := by
  rw [iteratedFDeriv_comp hg hf (by simp)]
  simp only [FormalMultilinearSeries.taylorComp, mixedCompositionBudget,
    Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
  change ‖iteratedFDeriv ℝ c.length g (f x)‖ *
    (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) f x‖) ≤ _
  have hp : (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) f x‖) ≤
      ∏ j, B (c.partSize j)*D^(c.partSize j) := by
    apply Finset.prod_le_prod₀
    · intro j _; exact norm_nonneg _
    · intro j _; exact hinner _ (c.partSize_pos j) (c.partSize_le j)
  have he : (∏ j, D^(c.partSize j)) = D^n := by
    simpa using c.prod_sigma_eq_prod (fun _ => D)
  calc
    _ ≤ C * (∏ j, B (c.partSize j)*D^(c.partSize j)) :=
      mul_le_mul (houter _ c.length_le) hp
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC
    _ = _ := by rw [Finset.prod_mul_distrib, he]; ring

end Falconer

end OAI
