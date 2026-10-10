import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cesàro means of the powers of a bounded operator. -/
def cesaro (S : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  ((n+1 : ℕ) : ℂ)⁻¹ • ∑ k ∈ Finset.range (n+1), S^k

omit [CompleteSpace H] in
lemma pow_norm_le_one [CompleteSpace H] (S : H →L[ℂ] H) (hS : ‖S‖≤1) (k : ℕ) : ‖S^k‖≤1 :=
by
  induction k with
  | zero =>
    rw [pow_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  | succ k ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (S^k),norm_nonneg S])

lemma cesaro_norm_le_one (S : H →L[ℂ] H) (hS : ‖S‖≤1) (n : ℕ) : ‖cesaro S n‖≤1 := by
  have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hs : ‖∑ k ∈ Finset.range (n+1), S^k‖≤(n+1:ℕ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖S^k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (1:ℝ) := Finset.sum_le_sum (fun k _ => pow_norm_le_one S hS k)
      _ = _ := by simp
  rw [cesaro,norm_smul,norm_inv]
  simp only [Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)).trans_eq (inv_mul_cancel₀ hn.ne')

lemma cesaro_apply_norm_le (S : H →L[ℂ] H) (hS : ‖S‖≤1) (n : ℕ) (x : H) :
    ‖cesaro S n x‖≤‖x‖ :=
  ((cesaro S n).le_opNorm x).trans (by nlinarith [cesaro_norm_le_one S hS n,norm_nonneg x])

omit [CompleteSpace H] in
lemma cesaro_mul_sub [CompleteSpace H] (S : H →L[ℂ] H) (n : ℕ) :
    cesaro S n*(1-S)=((n+1:ℕ):ℂ)⁻¹ • (1-S^(n+1)) := by
  rw [cesaro,smul_mul_assoc,geom_sum_mul_neg]

lemma cesaro_range_bound (S : H →L[ℂ] H) (hS : ‖S‖≤1) (n : ℕ) (x : H) :
    ‖cesaro S n ((1-S) x)‖≤((n+1:ℕ):ℝ)⁻¹*(2*‖x‖) := by
  have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hp : ‖(S^(n+1)) x‖≤‖x‖ :=
    ((S^(n+1)).le_opNorm x).trans (by nlinarith [pow_norm_le_one S hS (n+1),norm_nonneg x])
  have he := congrArg (fun T:H→L[ℂ]H => T x) (cesaro_mul_sub S n)
  simp only [mul_apply_eq_comp,smul_apply] at he
  rw [he,norm_smul,norm_inv]
  simp only [Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
  change ‖x-(S^(n+1)) x‖≤_
  exact (norm_sub_le _ _).trans (by linarith)

lemma cesaro_on_range (S : H →L[ℂ] H) (hS : ‖S‖≤1) (x : H) :
    Tendsto (fun n => cesaro S n ((1-S) x)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).mul_const (2*‖x‖)
  simp only [zero_mul,one_div] at ht
  apply squeeze_zero (fun n=>norm_nonneg _) (cesaro_range_bound S hS · x)
  simpa only [Nat.cast_add,Nat.cast_one] using ht

end Nonhyperlinear.Diffuseness

end

end OAI
