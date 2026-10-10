import OAI.NumberTheory.JointDickman.Analysis.CharacterUnsmoothing

namespace OAI

/-! # Discharge of the squarefree character estimate

For the two exponents used in the manuscript, uniform logarithmic cancellation
follows from the classical Siegel bound, the character Euler product, a regular
Perron contour, and bounded-coefficient unsmoothing.
-/
namespace JointDickman
open Complex Finset Filter

theorem squarefreeCharacterSum_norm_le_cutoff {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z Y : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hY : 0 ≤ Y) :
    ‖squarefreeCharacterSum χ z Y‖ ≤ Y := by
  unfold squarefreeCharacterSum
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊Y⌋₊, ‖(squarefreeWeight z n:ℂ)*χ (n:ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊Y⌋₊, (1:ℝ) :=
      sum_le_sum (fun n _ => squarefreeCharacterWeight_norm_le_one χ hz hz1 n)
    _ = (⌊Y⌋₊:ℝ) := by simp
    _ ≤ Y := Nat.floor_le hY

theorem squarefreeCharacterSum_all_cutoffs {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 3 ≤ Y → ∀ q : ℕ, ∀ [NeZero q],
      (q:ℝ) ≤ (Real.log Y)^C → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖squarefreeCharacterSum χ z Y‖ ≤ K*Y*(Real.log Y)^(-D) := by
  obtain ⟨K,hK,h⟩ := squarefreeCharacterSum_log_bound hz hz1 hC hD
  obtain ⟨X,hX⟩ := eventually_atTop.mp h
  let Y₀ := max X 3
  let K' := max K ((Real.log Y₀)^D)
  have hKK : K ≤ K' := le_max_left _ _
  have hK' : 0 ≤ K' := hK.le.trans hKK
  have hY₀ : 3 ≤ Y₀ := le_max_right _ _
  refine ⟨K',hK',?_⟩
  intro Y hY q _ hq χ hn
  have hY0 : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  by_cases hYY : Y₀ ≤ Y
  · have hb := hX Y ((le_max_left X 3).trans hYY) q χ hq hn
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK hY0.le) (Real.rpow_nonneg hlog.le _))
  · have hYY' : Y ≤ Y₀ := (lt_of_not_ge hYY).le
    have hp : (Real.log Y)^D ≤ K' :=
      (Real.rpow_le_rpow hlog.le (Real.log_le_log hY0 hYY') hD).trans (le_max_right _ _)
    have hfactor : 1 ≤ K'*(Real.log Y)^(-D) := by
      rw [Real.rpow_neg hlog.le, ←div_eq_mul_inv]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hlog D)).mpr (by simpa using hp)
    calc
      _ ≤ Y := squarefreeCharacterSum_norm_le_cutoff χ hz hz1 hY0.le
      _ ≤ (K'*(Real.log Y)^(-D))*Y := by
        simpa using mul_le_mul_of_nonneg_right hfactor hY0.le
      _ = _ := by ring

/-- Uniform logarithmic cancellation for squarefree character sums. -/
theorem squarefreeCharacterEstimateInput : PublishedInputs.SquarefreeCharacterEstimateInput := by
  intro z hz C D hC hD
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  exact squarefreeCharacterSum_all_cutoffs hz0 hz1 hC.le hD

end JointDickman

end OAI
