import OAI.Analysis.LipschitzHilbert.Phase.TiledPredictionIntegral

namespace OAI

/-! Assemble independently chosen current-cell predictors into the actual
finite line-mesh majorant for a good-path product. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace FiniteLineGrid

def patchedFactor (g : FiniteLineGrid) (level : ℕ)
    (F : Fin (g.branching ^ g.depth) → ℝ → ℝ) (x : ℝ) : ℝ := F (g.index level x) x

theorem patchedFactor_constant (g : FiniteLineGrid) {level : ℕ}
    (hl : level < g.depth) (F : Fin (g.branching ^ g.depth) → ℝ → ℝ)
    (hF : ∀ i x y, g.index (level + 1) x = g.index (level + 1) y → F i x = F i y)
    {x y : ℝ} (hxy : g.index (level + 1) x = g.index (level + 1) y) :
    g.patchedFactor level F x = g.patchedFactor level F y := by
  have hc : g.index level x = g.index level y := by
    rw [g.index_parent hl x, g.index_parent hl y, hxy]
  unfold patchedFactor
  rw [hc]
  exact hF _ x y hxy

theorem patchedFactor_average (g : FiniteLineGrid) (μ : Measure ℝ) (level : ℕ)
    (F : Fin (g.branching ^ g.depth) → ℝ → ℝ)
    (hF : ∀ i, (∫ x in {x | g.index level x = i}, F i x ∂μ) ≤
      μ.real {x | g.index level x = i})
    (i : Fin (g.branching ^ g.depth)) :
    (∫ x in {x | g.index level x = i}, g.patchedFactor level F x ∂μ) ≤
      μ.real {x | g.index level x = i} := by
  have heq : (∫ x in {x | g.index level x = i}, g.patchedFactor level F x ∂μ) =
      ∫ x in {x | g.index level x = i}, F i x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (g.measurable_index_fiber level i)] with x hx
    change g.index level x = i at hx
    simp only [patchedFactor, hx]
  rw [heq]
  exact hF i

end FiniteLineGrid

/-- The predictor at each coarse cell is patched by its actual mesh index.
The accumulated error is paid once through its sum, including on a good set. -/
theorem lineCellMajorant_of_local_predictions
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ) (hK : 0 < K)
    (good : Set ℝ) (beta error : ℕ → ℝ → ℝ)
    (F : ℕ → Fin (g.branching ^ g.depth) → ℝ → ℝ)
    (hF0 : ∀ n < g.depth, ∀ i x, 0 ≤ F n i x)
    (hconstant : ∀ n < g.depth, ∀ i x z,
      g.index (n + 1) x = g.index (n + 1) z → F n i x = F n i z)
    (haverage : ∀ n < g.depth, ∀ i,
      (∫ x in {x | g.index n x = i}, F n i x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index n x = i})
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ n < g.depth, 0 ≤ beta n x)
    (hcomparison : ∀ x ∈ g.root ∩ good, ∀ n < g.depth,
      beta n x ≤ Real.exp (error n x) * F n (g.index n x) x)
    (hbudget : ∀ x ∈ g.root ∩ good, (∑ n ∈ Finset.range g.depth, error n x) ≤ E) :
    Nonempty (LineCellMajorant g T K D y (Real.exp E)
      (good.indicator (fun x => T.weight K D (x, y + T.slope * x) *
        ∏ n ∈ Finset.range g.depth, beta n x))) := by
  refine ⟨{
    factor := fun n => g.patchedFactor n (F n)
    nonneg := fun n hn x => hF0 n hn _ x
    constant := fun n hn x z hxz => g.patchedFactor_constant hn (F n)
      (hconstant n hn) hxz
    average := fun n hn => g.patchedFactor_average _ n (F n) (haverage n hn)
    dominates := ?_ }⟩
  intro x hx
  by_cases hxgood : x ∈ good
  · rw [Set.indicator_of_mem hxgood]
    have hmem : x ∈ g.root ∩ good := ⟨hx, hxgood⟩
    have hprod := product_le_of_error_budget
      (fun n : Fin g.depth => beta n.val x)
      (fun n : Fin g.depth => g.patchedFactor n.val (F n.val) x)
      (fun n : Fin g.depth => error n.val x) E
      (fun n => hbeta x hmem n.val n.isLt)
      (fun n => hF0 n.val n.isLt _ x)
      (fun n => hcomparison x hmem n.val n.isLt)
      (by simpa only [Finset.sum_range] using hbudget x hmem)
    have hprod' : (∏ n ∈ Finset.range g.depth, beta n x) ≤
        Real.exp E * ∏ n ∈ Finset.range g.depth, g.patchedFactor n (F n) x := by
      simpa only [Finset.prod_range] using hprod
    have h := mul_le_mul_of_nonneg_left hprod'
      (T.weight_pos hK D (x, y + T.slope * x)).le
    simpa only [mul_left_comm] using h
  · rw [Set.indicator_of_notMem hxgood]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (T.weight_pos hK _ _).le
      (Finset.prod_nonneg fun n hn => hF0 n (Finset.mem_range.mp hn) _ x))

end LipschitzHilbert

end

end OAI
