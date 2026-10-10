import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-! # One loss parameter for radial pruning, row selection and endpoint counting -/

namespace Falconer

theorem exists_endpoint_radial_exponent (h : ℕ) :
    ∃ ell : ℝ, (h:ℝ) < ell ∧
      ell < (((h+1:ℕ):ℝ)/((h+1:ℕ)+1))*((h+1:ℕ):ℝ) := by
  let ell : ℝ := (h:ℝ)+1/(2*((h:ℝ)+2))
  have hp : 0 < (h:ℝ)+2 := by positivity
  have he : (((h+1:ℕ):ℝ)/((h+1:ℕ)+1))*((h+1:ℕ):ℝ) =
      (h:ℝ)+1/((h:ℝ)+2) := by
    push_cast
    field_simp
    ring
  refine ⟨ell,?_,?_⟩
  · dsimp [ell]
    exact lt_add_of_pos_right _ (one_div_pos.mpr (mul_pos (by norm_num) hp))
  · rw [he]
    dsimp [ell]
    have hi : 0 < 1/((h:ℝ)+2) := one_div_pos.mpr hp
    have hr : 1/(2*((h:ℝ)+2)) = (1/((h:ℝ)+2))/2 := by
      field_simp
    rw [hr]
    linarith

theorem exists_endpoint_count_exponent {s : ℝ} (hs : 3/2 < s) :
    ∃ a : ℝ, 0 < a ∧ 0 < 2*s-3-6*a := by
  refine ⟨(2*s-3)/12,by linarith,by linarith⟩

theorem exists_endpoint_selection_losses {ε c₁ c₂ g : ℝ}
    (hε : 0 < ε) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hg : 0 < g) :
    ∃ u τ : ℝ, 0 < u ∧ 0 < τ ∧ u < ε ∧ 30*u < τ ∧
      τ+10*u < c₁ ∧ τ+10*u < c₂ ∧ 280*u < g := by
  let τ : ℝ := min c₁ c₂/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ₁ : 2*τ ≤ c₁ := by dsimp [τ]; linarith [min_le_left c₁ c₂]
  have hτ₂ : 2*τ ≤ c₂ := by dsimp [τ]; linarith [min_le_right c₁ c₂]
  let u : ℝ := min ε (min (τ/100) (g/560))/2
  have hu : 0 < u := by dsimp [u]; positivity
  have huε : 2*u ≤ ε := by dsimp [u]; linarith [min_le_left ε (min (τ/100) (g/560))]
  have huτ : 2*u ≤ τ/100 := by
    dsimp [u]
    linarith [(min_le_right ε (min (τ/100) (g/560))).trans (min_le_left (τ/100) (g/560))]
  have hug : 2*u ≤ g/560 := by
    dsimp [u]
    linarith [(min_le_right ε (min (τ/100) (g/560))).trans (min_le_right (τ/100) (g/560))]
  exact ⟨u,τ,hu,hτ,by linarith,by linarith,by linarith,by linarith,by linarith⟩

end Falconer

end OAI
