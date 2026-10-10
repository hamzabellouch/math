import OAI.Geometry.Kahler.HartogsLiftedJets

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def block3 (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) : CMatrix :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0,0,r]

@[simp] lemma block3_horizontal (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (i j : Fin 2) :
    block3 A r i.castSucc j.castSucc = A i j := by
  fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma block3_vertical_left (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (j : Fin 2) :
    block3 A r 2 j.castSucc = 0 := by fin_cases j <;> rfl
@[simp] lemma block3_vertical_right (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (i : Fin 2) :
    block3 A r i.castSucc 2 = 0 := by fin_cases i <;> rfl
@[simp] lemma block3_vertical (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) : block3 A r 2 2 = r := rfl

lemma block3_one : block3 1 1 = (1 : CMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [block3, Matrix.one_apply]

lemma block3_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℂ) :
    block3 A r * block3 B s = block3 (A * B) (r*s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

lemma block3_inv {A : Matrix (Fin 2) (Fin 2) ℂ} {r : ℂ} (hA : A.det ≠ 0) (hr : r ≠ 0) :
    (block3 A r)⁻¹ = block3 A⁻¹ r⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [block3_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), mul_inv_cancel₀ hr]
  exact block3_one

@[simp] lemma verticalDelta_horizontal (i : Fin 2) : verticalDelta i.castSucc = 0 := by
  fin_cases i <;> simp [verticalDelta, Fin.ext_iff]
@[simp] lemma verticalDelta_vertical : verticalDelta 2 = 1 := rfl
@[simp] lemma horizontalIdentity_horizontal (i j : Fin 2) :
    horizontalIdentity i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases i <;> fin_cases j <;> norm_num [horizontalIdentity, Matrix.one_apply]
@[simp] lemma horizontalIdentity_vertical_left (i : Fin 3) : horizontalIdentity 2 i = 0 := by
  simp [horizontalIdentity]
@[simp] lemma horizontalIdentity_vertical_right (i : Fin 3) : horizontalIdentity i 2 = 0 := by
  simp [horizontalIdentity]

lemma normalPotential_hessian_block {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    complexHessian (normalPotential f lam w) (0,w) =
      block3 ((lam : ℂ) • 1 + (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)
        (barrierQ (normalLogWeight f w (0,w))) := by
  ext i j
  rw [normalPotential_hessian hf lam w hn]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    · simp [liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    · simp [liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
        Matrix.add_apply, Matrix.smul_apply]

lemma sum_fin3_horizontal (f : Fin 3 → ℂ) :
    (∑ i, f i) = (∑ i : Fin 2, f i.castSucc) + f 2 := by
  simpa using Fin.sum_univ_castSucc f

lemma block3_contraction (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (u v : Fin 3 → ℂ) :
    (∑ e, ∑ k, block3 A r e k * u e * v k) =
      (∑ e : Fin 2, ∑ k : Fin 2, A e k * u e.castSucc * v k.castSucc) + r * u 2 * v 2 := by
  rw [sum_fin3_horizontal]
  simp only [sum_fin3_horizontal, block3_horizontal, block3_vertical_left, block3_vertical_right,
    block3_vertical, zero_mul, Finset.sum_const_zero, zero_add, add_zero]

lemma barrierX_positive {s : ℝ} (hs : s < 0) : 0 < barrierX s :=
  div_pos (Real.exp_pos s) (sub_pos.mpr (Real.exp_lt_one_iff.mpr hs))

lemma barrierQ_positive {s : ℝ} (hs : s < 0) : 0 < barrierQ s := by
  dsimp [barrierQ]
  have := barrierX_positive hs
  positivity

end PinchedHartogs

end

end OAI
