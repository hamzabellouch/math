import OAI.Analysis.Pureness.Operators.ContinuousPositiveEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Set Filter
open scoped ComplexOrder NNReal Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem continuousNNRealCut_le_mul_of_support (f g : C(X, ℝ≥0))
    (hfg : ∀ x, 0 < f x → 0 < g x) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ x, f x-ε ≤ C*g x := by
  let K : Set X := {x | ε ≤ f x}
  have hK : IsCompact K := (isClosed_le continuous_const f.continuous).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne g.continuous.continuousOn
    have hgx : 0 < g x := hfg x (hε.trans_le hx)
    obtain ⟨C,hC⟩ := (isCompact_range f.continuous).bddAbove
    refine ⟨C/g x, ?_⟩
    intro y
    by_cases hy : y ∈ K
    · have hgy : g x ≤ g y := hmin hy
      calc
        f y-ε ≤ f y := tsub_le_self
        _ ≤ C := hC (mem_range_self y)
        _ = (C/g x)*g x := (div_mul_cancel₀ C hgx.ne').symm
        _ ≤ (C/g x)*g y := mul_le_mul_of_nonneg_left hgy bot_le
    · rw [tsub_eq_zero_of_le (le_of_not_ge hy)]
      exact bot_le
  · refine ⟨0,?_⟩
    intro x
    have hx : f x ≤ ε := le_of_not_ge (fun h => hne ⟨x,h⟩)
    simp only [tsub_eq_zero_of_le hx,zero_mul,le_refl]

theorem continuousNNRealPositive_cuntzBelow_of_support (f g : C(X, ℝ≥0))
    (hfg : ∀ x, 0 < f x → 0 < g x) :
    CuntzBelow (continuousNNRealPositive f) (continuousNNRealPositive g) := by
  apply CuntzBelow.of_tendsto (fun k => Positive.cut (Positive.rootExponent k) (continuousNNRealPositive f))
  · apply Positive.tendsto_cut
    simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0))
  · intro k
    obtain ⟨C,hC⟩ := continuousNNRealCut_le_mul_of_support f g hfg (Positive.rootExponent k) (Positive.rootExponent_pos k)
    apply CuntzBelow.of_le_smul _ _ C C.2
    rw [← continuousNNRealPositive_cut]
    intro x
    change ((((f x-Positive.rootExponent k : ℝ≥0) : ℝ) : ℂ)) ≤ (C : ℝ) • (((g x : ℝ) : ℂ))
    rw [Complex.real_smul]
    exact_mod_cast hC x
end CuntzPureness

end

end OAI
