import Mathlib.Basic.ENNReal.Basic

namespace OAI

/-! Finite binary subdivision used for the far-group mass estimate.
A bad child is bounded using its good parent; good children are subdivided
until the terminal scale. -/
noncomputable section
open scoped ENNReal
namespace LipschitzHilbert

def binaryChildCenter (c l : ℝ) (b : Bool) : ℝ :=
  if b then c+l/4 else c-l/4

theorem binary_density_bound (M V : ℝ → ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (good : ℕ → ℝ → ℝ → Prop)
    (hM : ∀ c l, 0 < l → M c l = M (c-l/4) (l/2)+M (c+l/4) (l/2))
    (hV : ∀ c l, 0 < l → V c l = V (c-l/4) (l/2)+V (c+l/4) (l/2))
    (hzero : ∀ c l, 0 < l → good 0 c l → M c l ≤ C*V c l)
    (hbad : ∀ n c l, 0 < l → good (n+1) c l → ∀ b,
      ¬good n (binaryChildCenter c l b) (l/2) →
        M (binaryChildCenter c l b) (l/2) ≤ C*V (binaryChildCenter c l b) (l/2)) :
    ∀ n c l, 0 < l → good n c l → M c l ≤ C*V c l := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    intro c l hl hg
    have hchild (b : Bool) : M (binaryChildCenter c l b) (l/2) ≤
        C*V (binaryChildCenter c l b) (l/2) := by
      by_cases hb : good n (binaryChildCenter c l b) (l/2)
      · exact ih _ _ (half_pos hl) hb
      · exact hbad n c l hl hg b hb
    rw [hM c l hl,hV c l hl,mul_add]
    exact add_le_add (hchild false) (hchild true)

end LipschitzHilbert

end

end OAI
