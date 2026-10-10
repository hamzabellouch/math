import OAI.MeasureTheory.Falconer.Recursion.RoundedProfilePieces

namespace OAI

/-! Choose the finite block-grid resolution after the decomposition scale
and all application error tolerances have been fixed. -/
namespace Falconer

theorem exists_profile_grid_threshold {τ ε σ ζ : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hσ : 0 < σ) (hζ : 0 < ζ) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
      2/(n : ℝ) ≤ τ/2 ∧ 4/(n : ℝ) ≤ ε*(τ/2) ∧
      16/((n : ℝ)*τ) ≤ σ ∧ 2/((n : ℝ)*τ) ≤ ζ := by
  have ha : 0 < 4/τ := by positivity
  have hb : 0 < 8/(ε*τ) := by positivity
  have hc : 0 < 16/(σ*τ) := by positivity
  have hd : 0 < 2/(ζ*τ) := by positivity
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (1+4/τ+8/(ε*τ)+16/(σ*τ)+2/(ζ*τ))
  have hn₀R : (0 : ℝ) < n₀ := by linarith
  have hn₀N : 0 < n₀ := by exact_mod_cast hn₀R
  refine ⟨n₀,hn₀N,?_⟩
  intro n hn
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := hn₀R.trans_le hnR
  have h1 : 4/τ ≤ n := by linarith
  have h2 : 8/(ε*τ) ≤ n := by linarith
  have h3 : 16/(σ*τ) ≤ n := by linarith
  have h4 : 2/(ζ*τ) ≤ n := by linarith
  have hm1 := (div_le_iff₀ hτ).mp h1
  have hm2 := (div_le_iff₀ (mul_pos hε hτ)).mp h2
  have hm3 := (div_le_iff₀ (mul_pos hσ hτ)).mp h3
  have hm4 := (div_le_iff₀ (mul_pos hζ hτ)).mp h4
  refine ⟨(div_le_iff₀ hnpos).2 ?_,(div_le_iff₀ hnpos).2 ?_,
    (div_le_iff₀ (mul_pos hnpos hτ)).2 ?_,(div_le_iff₀ (mul_pos hnpos hτ)).2 ?_⟩ <;> nlinarith

end Falconer

end OAI
