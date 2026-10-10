import OAI.Computability.DepthThree.RestrictionCostCorrelation
import OAI.Computability.DepthThree.RestrictionExpectedCost
import Mathlib.Tactic.Linarith

namespace OAI

universe uDepth1

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

def restrictionTheta (k b : ℕ) (p : ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc (b + 1) k, (k.choose l : ℝ) * (2 * p / (1 - p)) ^ l

theorem restrictionTheta_eq_reverseTheta (k b : ℕ) (p : ℝ) :
    restrictionTheta k b p = reverseTheta (2 * p / (1 - p)) b k := by
  have hs : (Finset.range (k + 1)).filter (fun l => b < l) = Finset.Icc (b + 1) k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  unfold reverseTheta
  rw [← Finset.sum_filter, hs]
  rfl

def cnfRestrictionCost (H : CNF V) (b : ℕ) (σ : Restriction V) : ℝ :=
  restrictionCost (cnfIndexFamily H.normalize) b σ

theorem cnfRestrictionCost_nonneg (H : CNF V) (b : ℕ) (σ : Restriction V) :
    0 ≤ cnfRestrictionCost H b σ :=
  restrictionCost_nonneg (cnfIndexFamily H.normalize) b σ

theorem cnf_restricted_correlation_le_cost (H : CNF V) (b : ℕ) (hb : 1 ≤ b)
    (σ : Restriction V) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * indicator (H.eval (fill σ x)))| ≤
      cnfRestrictionCost H b σ * corr b G := by
  have hn : ∀ i, (cnfIndexFamily H.normalize i).Normalized :=
    cnfIndexFamily_normalized (CNF.normalize_normalized H)
  simpa only [cnfRestrictionCost, indexedCNF_cnfIndexFamily_eval, CNF.eval_normalize] using
    restricted_correlation_le_cost (cnfIndexFamily H.normalize) b hb hn σ G

theorem restrictionAvg_cnfRestrictionCost_le (H : CNF V) (b k : ℕ)
    (hH : H.WidthAtMost k) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : restrictionTheta k b p < 1) :
    restrictionAvg p (cnfRestrictionCost H b) ≤ 1 / (1 - restrictionTheta k b p) := by
  have hn : ∀ i, (cnfIndexFamily H.normalize i).Normalized :=
    cnfIndexFamily_normalized (CNF.normalize_normalized H)
  have hw : ∀ i, (cnfIndexFamily H.normalize i).scope.card ≤ k :=
    cnfIndexFamily_width (CNF.normalize_widthAtMost hH)
  have ht : reverseTheta (2 * p / (1 - p)) b k < 1 := by
    simpa only [restrictionTheta_eq_reverseTheta] using hθ
  simpa +unfoldPartialApp only [cnfRestrictionCost, restrictionTheta_eq_reverseTheta, one_div] using
    restrictionAvg_restrictionCost_le (cnfIndexFamily H.normalize) p hp0 hp1 b k hn hw ht

theorem cnf_restriction_bound (H : CNF V) (b k : ℕ) (hb : 1 ≤ b)
    (hH : H.WidthAtMost k) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : restrictionTheta k b p < 1) :
    ∃ W : Restriction V → ℝ,
      (∀ σ, 0 ≤ W σ) ∧
      restrictionAvg p W ≤ 1 / (1 - restrictionTheta k b p) ∧
      ∀ (σ : Restriction V) (G : Cube (Live σ) → ℝ),
        |finiteAvg (fun x => G x * indicator (H.eval (fill σ x)))| ≤ W σ * corr b G := by
  refine ⟨cnfRestrictionCost H b, cnfRestrictionCost_nonneg H b, ?_, ?_⟩
  · exact restrictionAvg_cnfRestrictionCost_le H b k hH p hp0 hp1 hθ
  · exact cnf_restricted_correlation_le_cost H b hb

theorem restrictionAvg_cnfRestrictionCost_le_two (H : CNF V) (b k : ℕ)
    (hH : H.WidthAtMost k) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : restrictionTheta k b p ≤ 1 / 2) :
    restrictionAvg p (cnfRestrictionCost H b) ≤ 2 := by
  have ht : restrictionTheta k b p < 1 := by linarith
  have hd : 0 < 1 - restrictionTheta k b p := sub_pos.mpr ht
  refine (restrictionAvg_cnfRestrictionCost_le H b k hH p hp0 hp1 ht).trans ?_
  apply (div_le_iff₀ hd).mpr
  linarith

end DepthThreeLowerBound

end

end OAI
