import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalFieldDifferences
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFieldBounds

namespace OAI

/-! Fixed polynomial precision parameters for coordinate differences of
the manufactured field. Both the spatial step and scalar accuracy are
chosen from its already proved uniform six-derivative bound. -/

noncomputable section
namespace ContinuumCoulomb.MoserDifferenceBudget

def guard : ℕ := ⌈manufacturedFieldDerivativeConstant⌉₊+1

theorem guard_positive : 0 < guard := by unfold guard; omega

theorem guard_bound : manufacturedFieldDerivativeConstant ≤ (guard:ℝ) := by
  have h := Nat.le_ceil manufacturedFieldDerivativeConstant
  unfold guard
  push_cast
  linarith

def step (P : ℕ) : ℚ := (16*(guard:ℚ)*(P+1))⁻¹
def precision (P : ℕ) : ℕ := 16384*guard^2*(P+1)^3

theorem step_positive (P : ℕ) : 0 < step P := by
  have hg : (0:ℚ) < guard := by exact_mod_cast guard_positive
  unfold step
  positivity

theorem step_le_one (P : ℕ) : (step P:ℝ) ≤ 1 := by
  have hg : (1:ℝ) ≤ guard := by exact_mod_cast guard_positive
  have hp : (1:ℝ) ≤ (P:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) P]
  simp only [step,Rat.cast_inv,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add,Rat.cast_one]
  apply (inv_le_one₀ (by positivity)).mpr
  nlinarith

theorem second_budget (P : ℕ) :
    (guard:ℝ)*(step P:ℝ)+4*((precision P:ℝ)+1)⁻¹/(step P:ℝ)^2 ≤
      (8*((P:ℝ)+1))⁻¹ := by
  let B : ℝ := guard
  let Q : ℝ := (P:ℝ)+1
  have hB : 0 < B := by dsimp [B]; exact_mod_cast guard_positive
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hs : (step P:ℝ) = (16*B*Q)⁻¹ := by
    simp only [step,Rat.cast_inv,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add,Rat.cast_one,B,Q]
  have hp : (precision P:ℝ) = 16384*B^2*Q^3 := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one,B,Q]
  have hbase : 0 < 16384*B^2*Q^3 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hB)) (pow_pos hQ _)
  have he : ((precision P:ℝ)+1)⁻¹ ≤ (16384*B^2*Q^3)⁻¹ := by
    rw [hp]
    apply inv_anti₀ hbase
    linarith
  rw [hs]
  change B*(16*B*Q)⁻¹+4*((precision P:ℝ)+1)⁻¹/((16*B*Q)⁻¹)^2 ≤ (8*Q)⁻¹
  calc
    _ ≤ B*(16*B*Q)⁻¹+4*(16384*B^2*Q^3)⁻¹/((16*B*Q)⁻¹)^2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (by norm_num)) (sq_nonneg _))
    _ = _ := by
      field_simp [hB.ne',hQ.ne']
      norm_num

theorem first_budget (P : ℕ) :
    (guard:ℝ)*(step P:ℝ)+2*((precision P:ℝ)+1)⁻¹/(step P:ℝ) ≤
      (8*((P:ℝ)+1))⁻¹ := by
  have hs : (0:ℝ) < step P := by exact_mod_cast step_positive P
  have hs1 := step_le_one P
  have hcoeff : 2/(step P:ℝ) ≤ 4/(step P:ℝ)^2 := by
    apply (div_le_div_iff₀ hs (sq_pos_of_pos hs)).mpr
    have hh2 := mul_le_mul_of_nonneg_left hs1 hs.le
    nlinarith only [hh2,hs.le]
  have h := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ ((precision P:ℝ)+1)⁻¹ by positivity)
  have hnoise : 2*((precision P:ℝ)+1)⁻¹/(step P:ℝ) ≤
      4*((precision P:ℝ)+1)⁻¹/(step P:ℝ)^2 := by
    convert h using 1 <;> ring
  exact (add_le_add le_rfl hnoise).trans (second_budget P)

theorem laplacian_budget (P : ℕ) :
    3*((guard:ℝ)*(step P:ℝ)+4*((precision P:ℝ)+1)⁻¹/(step P:ℝ)^2) ≤
      ((P:ℝ)+1)⁻¹ := by
  have h := mul_le_mul_of_nonneg_left (second_budget P) (by norm_num : (0:ℝ) ≤ 3)
  apply h.trans
  rw [mul_inv]
  norm_num
  have hp : 0 ≤ ((P:ℝ)+1)⁻¹ := by positivity
  linarith

end ContinuumCoulomb.MoserDifferenceBudget

end

end OAI
