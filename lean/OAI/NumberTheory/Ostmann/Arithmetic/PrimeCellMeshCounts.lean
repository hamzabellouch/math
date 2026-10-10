import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget
import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellMeshBudget
open ScaleBudget Filter

def meshWidth (r : Row) (L : ℝ) : ℝ := Real.exp (-Real.exp (r.δ*L))

def meshIntervals (r : Row) (L : ℝ) : ℕ :=
  ⌈Real.exp (r.a₁*L)/meshWidth r L⌉₊+1

lemma row_a₁_pos (r : Row) : 0 < r.a₁ := by
  linarith [r.μ_pos,r.μ_lt_δ,r.δ_lt_δ',r.δ'_lt_θ,r.zero_gap,r.range]

lemma mesh_ratio (r : Row) (L : ℝ) :
    Real.exp (r.a₁*L)/meshWidth r L = Real.exp (r.a₁*L+Real.exp (r.δ*L)) := by
  rw [meshWidth,← Real.exp_sub]
  congr 1
  ring

lemma meshIntervals_pos (r : Row) (L : ℝ) : 0 < meshIntervals r L := by
  unfold meshIntervals
  omega

theorem log_meshIntervals_le (r : Row) {L : ℝ} (hL : 0 ≤ L) :
    Real.log (meshIntervals r L : ℝ) ≤ Real.exp (r.δ*L)+r.a₁*L+Real.log 4 := by
  have ha := row_a₁_pos r
  have hbase : 1 ≤ Real.exp (r.a₁*L+Real.exp (r.δ*L)) :=
    Real.one_le_exp (by positivity)
  have hceil := Nat.ceil_lt_add_one (Real.exp_nonneg (r.a₁*L+Real.exp (r.δ*L)))
  have hN : (meshIntervals r L : ℝ) ≤ 4*Real.exp (r.a₁*L+Real.exp (r.δ*L)) := by
    rw [meshIntervals,mesh_ratio,Nat.cast_add,Nat.cast_one]
    linarith
  have hNp : (0:ℝ) < meshIntervals r L := by exact_mod_cast meshIntervals_pos r L
  have hh := Real.log_le_log hNp hN
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith

theorem log_joint_mesh_card_le (r : Row) {L : ℝ} (hL : 0 ≤ L)
    (n M : ℕ) (hM : 0 < M) (hmod : Real.log (M:ℝ) ≤ Real.exp (r.μ*L)) :
    Real.log (((meshIntervals r L)^n*M^n : ℕ):ℝ) ≤
      (n:ℝ)*(Real.exp (r.δ*L)+r.a₁*L+Real.log 4+Real.exp (r.μ*L)) := by
  have hNp : (0:ℝ) < meshIntervals r L := by exact_mod_cast meshIntervals_pos r L
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  push_cast
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  have h1 := mul_le_mul_of_nonneg_left (log_meshIntervals_le r hL) (Nat.cast_nonneg n : (0:ℝ)≤n)
  have h2 := mul_le_mul_of_nonneg_left hmod (Nat.cast_nonneg n : (0:ℝ)≤n)
  linarith

end Ostmann.Arithmetic.PrimeCellMeshBudget

end

end OAI
