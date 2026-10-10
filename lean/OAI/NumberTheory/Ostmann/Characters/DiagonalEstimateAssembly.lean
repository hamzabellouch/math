import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateChangingBudget
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateChangingSum
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateGapBudget
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourcePreserving

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem exists_sourceDiagonal_assembly (d : Decomposition) (B₁ : ℝ)
    {δ α β ρ γ c₀ c : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∃BD0 : ℝ,0 < BD0 ∧ ∀BD : ℝ,BD0 ≤ BD →
      ∀ᶠ k : ℕ in atTop,∀Kpair cpair αpair : ℝ,0 < cpair → 0 < αpair →
      ∀ᶠ L : ℝ in atTop,
      ∀E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j : ℕ,∀hj : j<k,∀B V : (l:ℕ) → State k (l+1) → ℤ,
      (∀P∈sourcePivotRanges w j,
        ∀e∈Finset.univ\codePreservingMatchings w.configuration (wordSize k L) j,
        ∀h h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,
        ‖sourceHistoryPairMean w j hj B V P e h h'‖ ≤
          Real.exp (Kpair*L^2-cpair*Real.exp (αpair*L))) →
      ∀loss : ℝ,loss ≤ (wordSize k L:ℝ) →
        sourceUnitDiagonal w j hj B V ≤
          (1/2:ℝ)*Real.exp (-loss)*Real.exp (-2*B₁*(2:ℝ)^j*(wordSize k L:ℝ)) := by
  let BD0 := max 1 (diagonalGapThreshold B₁ β (|Real.log ρ|+2))
  refine ⟨BD0,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro BD hBD
  have hBDpos : 0 < BD := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hBD)
  have hBDgap : diagonalGapThreshold B₁ β (|Real.log ρ|+2) ≤ BD :=
    (le_max_right _ _).trans hBD
  filter_upwards [eventually_sourcePreservingAverage_le (δ:=δ) d hα hαβ hρ hγ hc₀ hc,
    eventually_fixedConfiguration_changing_budget (δ:=δ) d hα hαβ hρ hγ hc₀ hc]
    with k hgood hcost
  obtain ⟨Kcost,hKcost,hcost⟩ := hcost BD hBDpos.le
  intro Kpair cpair αpair hcpair hαpair
  filter_upwards [hgood BD hBDpos,hcost,
    eventually_diagonal_gap_budget B₁ β (|Real.log ρ|+2) BD
      (sourceDiagonalOverhead k c c₀) (Kcost+Kpair) k hcpair hαpair hBDgap]
    with L hgood hcost hgap
  intro E hE hband s w j hj B V hpair loss hloss
  have hbad := sourceChangingAverage_le_of_pair_norm w j hj B V
    (Real.exp_pos (Kpair*L^2-cpair*Real.exp (αpair*L))).le hpair
  have hbad' : sourceChangingAverage w j hj B V ≤
      Real.exp ((Kcost+Kpair)*L^2-cpair*Real.exp (αpair*L)) := by
    apply hbad.trans
    have hh := mul_le_mul_of_nonneg_right (hcost E hE s w j hj.le)
      (Real.exp_pos (Kpair*L^2-cpair*Real.exp (αpair*L))).le
    apply hh.trans_eq
    rw [←Real.exp_add]
    congr 1
    ring
  rw [sourceUnitDiagonal_partition]
  exact (add_le_add (hgood E hE hband s w j hj B V) hbad').trans (hgap j hj loss hloss)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
