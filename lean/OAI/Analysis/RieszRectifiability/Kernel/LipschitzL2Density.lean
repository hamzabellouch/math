import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteStepLp

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem bounded_lipschitz_L2_approximation {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0),
      HasCompactSupport g ∧ LipschitzWith K g ∧ (∀ x, |g x| ≤ (B : ℝ)) ∧
        MemLp g 2 μ ∧ eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hgcompact, hgsmooth, herror⟩ :=
    hf.exist_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hε
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgcompact hgsmooth (by simp)
  obtain ⟨B, hB⟩ := hgcompact.exists_bound_of_continuous hgsmooth.continuous
  refine ⟨g, K, Real.toNNReal B, hgcompact, hK, ?_,
    hgsmooth.continuous.memLp_of_hasCompactSupport hgcompact, herror⟩
  intro x
  have hbound : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using! hB x
  exact hbound.trans (Real.le_coe_toNNReal B)

theorem bounded_lipschitz_L2_squared_approximation {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0),
      HasCompactSupport g ∧ LipschitzWith K g ∧ (∀ x, |g x| ≤ (B : ℝ)) ∧
        MemLp g 2 μ ∧ (∫ x, (g x - f x) ^ 2 ∂μ) ≤ ε ^ 2 := by
  obtain ⟨g, K, B, hcomp, hLip, hbound, hg, he⟩ :=
    bounded_lipschitz_L2_approximation μ f hf ε hε
  refine ⟨g, K, B, hcomp, hLip, hbound, hg, ?_⟩
  have hnorm : ‖(hf.sub hg).toLp (f - g)‖ ≤ ε := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hε.le he
  have hsq := pow_le_pow_left₀ (norm_nonneg ((hf.sub hg).toLp (f - g))) hnorm 2
  rw [toLp_norm_sq_eq_integral] at hsq
  simpa only [Pi.sub_apply, sub_sq_comm] using! hsq

theorem exists_bounded_lipschitz_L2_sequence {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) :
    ∃ (g : ℕ → Ambient d → ℝ) (K B : ℕ → ℝ≥0),
      (∀ k, HasCompactSupport (g k)) ∧ (∀ k, LipschitzWith (K k) (g k)) ∧
      (∀ k x, |g k x| ≤ (B k : ℝ)) ∧ (∀ k, MemLp (g k) 2 μ) ∧
      Tendsto (fun k => ∫ x, (g k x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have happrox : ∀ k : ℕ, ∃ (g : Ambient d → ℝ) (K B : ℝ≥0),
      HasCompactSupport g ∧ LipschitzWith K g ∧ (∀ x, |g x| ≤ (B : ℝ)) ∧
        MemLp g 2 μ ∧ (∫ x, (g x - f x) ^ 2 ∂μ) ≤ ((1 / 2 : ℝ) ^ k) ^ 2 := by
    intro k
    exact bounded_lipschitz_L2_squared_approximation μ f hf _ (by positivity)
  choose g K B hcomp hLip hbound hg herr using happrox
  refine ⟨g, K, B, hcomp, hLip, hbound, hg, ?_⟩
  apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) herr
  simpa only [zero_pow two_ne_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).pow 2

end

end RieszRectifiability

end OAI
