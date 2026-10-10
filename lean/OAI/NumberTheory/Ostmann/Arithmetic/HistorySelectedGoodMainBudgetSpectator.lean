import OAI.NumberTheory.Ostmann.Tree.TreeComparison

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedGoodMainBudget
open Filter

def treeCost (k : ℕ) : ℝ :=
  1 + ∑ l ∈ Finset.range (k+1), Tree.treeComparisonConstant (l-2)

theorem treeCost_pos (k : ℕ) : 0 < treeCost k := by
  have hs : 0 ≤ ∑ l ∈ Finset.range (k+1), Tree.treeComparisonConstant (l-2) :=
    Finset.sum_nonneg (fun l _ => Tree.treeComparisonConstant_nonneg _)
  unfold treeCost
  linarith

theorem treeComparisonConstant_le {k l : ℕ} (hl : l ≤ k) :
    Tree.treeComparisonConstant (l-2) ≤ treeCost k := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (k+1)) => Tree.treeComparisonConstant_nonneg (j-2))
    (show l ∈ Finset.range (k+1) by simpa using Nat.lt_succ_of_le hl)
  unfold treeCost
  linarith

theorem eventually_quarterPower_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℕ, 0 < q →
      Real.exp (L/2000) ≤ Real.log (q:ℝ) → (q:ℝ)^(-(1/4:ℝ)) ≤ ε := by
  have ht : Tendsto (fun L : ℝ => Real.exp (L/2000)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2000))
  filter_upwards [ht.eventually_ge_atTop (-4*Real.log ε)] with L hL
  intro q hq hlog
  rw [Real.rpow_def_of_pos (by exact_mod_cast hq)]
  calc
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by nlinarith)
    _ = ε := Real.exp_log hε

theorem exists_spectator_product_small (k : ℕ) (R : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (l : ℕ), l ≤ k → ∀ (ι : Type) [Fintype ι] (q : ι → ℕ) (c : ι → ℝ),
      (∀ i, 0 < q i) → (∀ i, Real.exp (L/2000) ≤ Real.log (q i:ℝ)) →
      (∀ i, 0 ≤ c i) → (∀ i, c i ≤ ε) →
      (∏ i, Tree.treeComparisonConstant (l-2)*(c i+(q i:ℝ)^(-(1/4:ℝ)))) ≤
        Real.exp (-R*(Fintype.card ι:ℝ)) := by
  let ε := Real.exp (-R)/(2*treeCost k)
  have hε : 0 < ε := div_pos (Real.exp_pos _) (mul_pos (by norm_num) (treeCost_pos k))
  refine ⟨ε, hε, ?_⟩
  filter_upwards [eventually_quarterPower_le ε hε] with L hL
  intro l hl ι _ q c hq hlog hc hcε
  have ht : Tree.treeComparisonConstant (l-2)*(2*ε) ≤ Real.exp (-R) := by
    calc
      _ ≤ treeCost k*(2*ε) := mul_le_mul_of_nonneg_right
        (treeComparisonConstant_le hl) (by positivity)
      _ = _ := by dsimp only [ε]; field_simp [(treeCost_pos k).ne']
  calc
    _ ≤ ∏ _i : ι, Real.exp (-R) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (Tree.treeComparisonConstant_nonneg _)
          (add_nonneg (hc i) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro i _
        apply le_trans _ ht
        apply mul_le_mul_of_nonneg_left _ (Tree.treeComparisonConstant_nonneg _)
        linarith [hL (q i) (hq i) (hlog i), hcε i]
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      congr 1
      ring

end Ostmann.Arithmetic.HistorySelectedGoodMainBudget

end

end OAI
