import OAI.NumberTheory.TotientAsymptotic.NormalityIntervals

namespace OAI

/-! Exact double-logarithmic grid for reducing normality to finitely many intervals. -/
noncomputable section
namespace TotientAsymptotic

def normalityGridPoint (j : ℕ) : ℝ := Real.exp (Real.exp j)

lemma normalityGridPoint_B (j : ℕ) : B (normalityGridPoint j) = j := by
  simp [normalityGridPoint,B]

lemma normalityGridPoint_mono : StrictMono normalityGridPoint := by
  intro i j hij
  apply Real.exp_lt_exp.mpr
  apply Real.exp_lt_exp.mpr
  exact_mod_cast hij

lemma normalityGridPoint_one_lt (j : ℕ) : 1<normalityGridPoint j :=
  Real.one_lt_exp_iff.mpr (Real.exp_pos _)

lemma normalityGridPoint_bracket {x : ℝ} (hx : 1<x) (hB : 0≤B x) :
    normalityGridPoint ⌊B x⌋₊ ≤ x ∧ x < normalityGridPoint (⌊B x⌋₊+1) := by
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have he : Real.exp (Real.exp (B x))=x := by
    simp only [B,Real.exp_log hlog,Real.exp_log hx0]
  constructor
  · calc
      _ ≤ Real.exp (Real.exp (B x)) := by
        apply Real.exp_le_exp.mpr
        apply Real.exp_le_exp.mpr
        exact Nat.floor_le hB
      _ = x := he
  · calc
      x = Real.exp (Real.exp (B x)) := he.symm
      _ < _ := by
        apply Real.exp_lt_exp.mpr
        apply Real.exp_lt_exp.mpr
        simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (B x)

end TotientAsymptotic

end

end OAI
