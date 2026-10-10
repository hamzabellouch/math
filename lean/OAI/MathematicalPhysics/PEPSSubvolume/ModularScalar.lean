import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Dimension-free row-column and scalar modular distortion bounds. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open PolynomialPEPS.PinnedEntropy

open scoped BigOperators Matrix.Norms.L2Operator
namespace PolynomialPEPS.Subvolume.MatrixRows
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
lemma column_l2 (A : Matrix ι κ ℂ) (j : κ) :
    Real.sqrt (∑ i, ‖A i j‖^2) ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (PiLp.single 2 j (1 : ℂ))
  have hx : ‖(PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ κ)‖ = 1 := by simp
  rw [hx,mul_one] at h
  have he : (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ (PiLp.single 2 j (1 : ℂ))) =
      WithLp.toLp 2 (fun i => A i j) := by
    ext i
    change (A *ᵥ Pi.single j (1 : ℂ)) i = A i j
    simp only [Matrix.mulVec_single,MulOpposite.op_one,one_smul]
    rfl
  rw [he,EuclideanSpace.norm_eq] at h
  exact h

lemma row_l2 (A : Matrix ι κ ℂ) (i : ι) :
    Real.sqrt (∑ j, ‖A i j‖^2) ≤ ‖A‖ := by
  simpa [Matrix.conjTranspose_apply, Matrix.l2_opNorm_conjTranspose] using column_l2 A.conjTranspose i

lemma row_product (A B : Matrix ι κ ℂ) (i : ι) :
    ∑ j, ‖A i j‖ * ‖B i j‖ ≤ ‖A‖ * ‖B‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => ‖A i j‖) (fun j => ‖B i j‖)
  exact h.trans (mul_le_mul (row_l2 A i) (row_l2 B i) (Real.sqrt_nonneg _) (norm_nonneg _))

lemma column_product (A B : Matrix ι κ ℂ) (j : κ) :
    ∑ i, ‖A i j‖ * ‖B i j‖ ≤ ‖A‖ * ‖B‖ := by
  simpa [Matrix.conjTranspose_apply, Matrix.l2_opNorm_conjTranspose] using
    row_product A.conjTranspose B.conjTranspose j

theorem weighted_sum (A B : Matrix ι ι ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∑ i, ∑ j, max (p i) (p j) * (‖A i j‖ * ‖B i j‖) ≤
      2 * (∑ i, p i) * (‖A‖ * ‖B‖) := by
  calc
    _ ≤ ∑ i, ∑ j, (p i+p j) * (‖A i j‖ * ‖B i j‖) := by
      gcongr with i j
      exact max_le (le_add_of_nonneg_right (hp j)) (le_add_of_nonneg_left (hp i))
    _ = (∑ i, p i * (∑ j, ‖A i j‖ * ‖B i j‖)) +
        (∑ j, p j * (∑ i, ‖A i j‖ * ‖B i j‖)) := by
      simp_rw [add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ (∑ i, p i * (‖A‖*‖B‖)) + (∑ j, p j * (‖A‖*‖B‖)) := by
      exact add_le_add
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (row_product A B i) (hp i))
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (column_product A B j) (hp j))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem coefficient_sum (A B : Matrix ι ι ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (d : ι → ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ i j, ‖d i j‖ ≤ C * max (p i) (p j)) :
    ‖∑ i, ∑ j, d i j * A i j * B i j‖ ≤
      2*C*(∑ i, p i)*(‖A‖*‖B‖) := by
  calc
    _ ≤ ∑ i, ∑ j, ‖d i j * A i j * B i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, C*max (p i) (p j) * (‖A i j‖*‖B i j‖) := by
      simp only [norm_mul]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hd i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = C * (∑ i, ∑ j, max (p i) (p j) * (‖A i j‖*‖B i j‖)) := by
      simp_rw [Finset.mul_sum]
      congr 1
      ext i
      congr 1
      ext j
      ring
    _ ≤ C * (2*(∑ i, p i)*(‖A‖*‖B‖)) := mul_le_mul_of_nonneg_left (weighted_sum A B p hp) hC
    _ = _ := by ring

end PolynomialPEPS.Subvolume.MatrixRows

namespace PolynomialPEPS.Subvolume.ModularScalar

lemma even_exp_remainder (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x + Real.exp (-x) - 2 ≤ x^2 * Real.exp x := by
  let y := Real.exp (x/2)
  let z := Real.exp (-x/2)
  have hy : 0 < y := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  have hyz : y*z=1 := by
    dsimp [y,z]
    rw [← Real.exp_add, ← add_div, add_neg_cancel, zero_div, Real.exp_zero]
  have hysq : y^2 = Real.exp x := by
    dsimp [y]
    rw [sq,← Real.exp_add]
    congr 1
    ring
  have hzsq : z^2 = Real.exp (-x) := by
    dsimp [z]
    rw [sq,← Real.exp_add]
    congr 1
    ring
  have hd0 : 0 ≤ y-z := sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have he := Real.add_one_le_exp (-x)
  have hmul : y*Real.exp (-x) = z := by
    dsimp [y,z]
    rw [← Real.exp_add]
    congr 1
    ring
  have hd : y-z ≤ x*y := by
    have ht := mul_le_mul_of_nonneg_left he hy.le
    rw [hmul] at ht
    nlinarith
  have hs := sq_le_sq₀ hd0 (mul_nonneg hx hy.le) |>.mpr hd
  rw [mul_pow,hysq] at hs
  nlinarith [sq_nonneg (y-z)]

lemma polynomial_exp_decay (x : ℝ) (hx : 0 ≤ x) :
    x^2 * Real.exp (-x/4) ≤ 32 := by
  have hp := Real.pow_div_factorial_le_exp (x/4) (show 0 ≤ x/4 by positivity) 2
  norm_num at hp
  have he : Real.exp (x/4)*Real.exp (-x/4) = 1 := by
    rw [← Real.exp_add, ← add_div, add_neg_cancel, zero_div, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-x/4)).le
  nlinarith

theorem quadratic_log_ratio (x a : ℝ) (hx : 0 ≤ x) (ha : |a| ≤ 1/4) :
    Real.exp (-x/2) * (Real.exp (a*x) + Real.exp (-a*x) - 2) ≤ 32*a^2 := by
  have heven : Real.exp (a*x) + Real.exp (-a*x) =
      Real.exp (|a| * x) + Real.exp (-(|a| * x)) := by
    rcases le_total 0 a with h|h
    · simp [abs_of_nonneg h]
    · simp [abs_of_nonpos h,add_comm]
  rw [heven]
  have ht := mul_le_mul_of_nonneg_left (even_exp_remainder (|a| * x) (by positivity))
    (Real.exp_pos (-x/2)).le
  have hcomb : Real.exp (-x/2) * ((|a| * x)^2 * Real.exp (|a| * x)) =
      a^2 * (x^2 * Real.exp ((|a|-1/2)*x)) := by
    rw [mul_pow,sq_abs]
    calc
      _ = a^2*x^2*(Real.exp (-x/2)*Real.exp (|a| * x)) := by ring
      _ = _ := by
        rw [← Real.exp_add,
          show -x/2 + |a| * x = (|a|-1/2)*x by ring]
        ring
  rw [hcomb] at ht
  have he : Real.exp ((|a|-1/2)*x) ≤ Real.exp (-x/4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ a^2 * (x^2 * Real.exp ((|a|-1/2)*x)) := ht
    _ ≤ a^2 * (x^2 * Real.exp (-x/4)) := by gcongr
    _ ≤ a^2 * 32 := mul_le_mul_of_nonneg_left (polynomial_exp_decay x hx) (sq_nonneg a)
    _ = 32*a^2 := by ring

end PolynomialPEPS.Subvolume.ModularScalar

namespace PolynomialPEPS.Subvolume.ModularScalar

lemma positive_weight_bound (s t a : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ha : |a| ≤ 1/4) :
    Real.sqrt (s*t) * ((s/t)^a+(t/s)^a-2) ≤ 32*a^2*max s t := by
  suffices hordered : ∀ s t : ℝ, 0 < s → 0 < t → t ≤ s →
      Real.sqrt (s*t) * ((s/t)^a+(t/s)^a-2) ≤ 32*a^2*s by
    rcases le_total t s with h|h
    · simpa only [max_eq_left h] using hordered s t hs ht h
    · simpa only [max_eq_right h,mul_comm s t,add_comm ((s/t)^a) ((t/s)^a)] using
        hordered t s ht hs h
  intro s t hs ht hts
  let x := Real.log s - Real.log t
  have hx : 0 ≤ x := sub_nonneg.mpr (Real.log_le_log ht hts)
  have hst : (s/t)^a = Real.exp (a*x) := by
    rw [Real.rpow_def_of_pos (div_pos hs ht),Real.log_div hs.ne' ht.ne']
    congr 1
    dsimp [x]
    ring
  have hts' : (t/s)^a = Real.exp (-a*x) := by
    rw [Real.rpow_def_of_pos (div_pos ht hs),Real.log_div ht.ne' hs.ne']
    congr 1
    dsimp [x]
    ring
  have hroot : Real.sqrt (s*t) = s*Real.exp (-x/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (mul_pos hs ht),Real.log_mul hs.ne' ht.ne']
    nth_rw 2 [← Real.exp_log hs]
    rw [← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  rw [hst,hts',hroot,mul_assoc]
  calc
    _ ≤ s*(32*a^2) := mul_le_mul_of_nonneg_left (quadratic_log_ratio x a hx ha) hs.le
    _ = _ := by ring

def modularCoefficient (s t a : ℝ) : ℝ :=
  if 0 < s ∧ 0 < t then Real.sqrt (s*t) * ((s/t)^a+(t/s)^a-2)/2 else 0

lemma modularCoefficient_nonneg (s t a : ℝ) : 0 ≤ modularCoefficient s t a := by
  unfold modularCoefficient
  split_ifs with h
  · have h₁ := Real.add_one_le_exp (Real.log (s/t)*a)
    have h₂ := Real.add_one_le_exp (Real.log (t/s)*a)
    have hlog : Real.log (t/s) = -Real.log (s/t) := by
      rw [Real.log_div h.2.ne' h.1.ne',Real.log_div h.1.ne' h.2.ne']
      ring
    have hexp : 0 ≤ (s/t)^a+(t/s)^a-2 := by
      rw [Real.rpow_def_of_pos (div_pos h.1 h.2),Real.rpow_def_of_pos (div_pos h.2 h.1)]
      rw [hlog] at h₂ ⊢
      nlinarith
    positivity
  · rfl

theorem modularCoefficient_bound (s t a : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : |a| ≤ 1/4) :
    |modularCoefficient s t a| ≤ 16*a^2*max s t := by
  rw [abs_of_nonneg (modularCoefficient_nonneg s t a)]
  unfold modularCoefficient
  split_ifs with h
  · have H := positive_weight_bound s t a h.1 h.2 ha
    linarith
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a))
      (by simpa using max_le_max hs ht)

end PolynomialPEPS.Subvolume.ModularScalar

namespace PolynomialPEPS.Subvolume.ModularScalar

lemma modularCoefficient_formula (s t a : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.sqrt s * Real.sqrt t * (((s^a)*(t^a)⁻¹ + (s^a)⁻¹*(t^a))/2 - 1) =
      modularCoefficient s t a := by
  by_cases hs0 : s=0
  · simp [hs0,modularCoefficient]
  by_cases ht0 : t=0
  · simp [ht0,modularCoefficient]
  have hs' : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have ht' : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  rw [modularCoefficient,ite_eq_left ⟨hs',ht'⟩,← Real.sqrt_mul hs,
    Real.div_rpow hs ht,Real.div_rpow ht hs]
  ring

end PolynomialPEPS.Subvolume.ModularScalar

end

end OAI
