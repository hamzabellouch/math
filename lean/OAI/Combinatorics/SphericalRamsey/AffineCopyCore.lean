import OAI.Combinatorics.SphericalRamsey.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

namespace OAI

noncomputable section
open scoped RealInnerProductSpace
namespace GrahamSpherical

/-- Polarization in the actual real Euclidean inner product. -/
lemma inner_sub_self (n : ℕ) (x y : Point n) :
    (inner ℝ (x-y) (x-y)) = (inner ℝ (x) (x)) - 2*(inner ℝ (x) (y)) + (inner ℝ (y) (y)) := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y x]
  ring

/-- An orthonormal pair reconstructs a vector once its two coordinates account
for its full squared norm. No dimension assumption is imposed on the codomain. -/
lemma vector_eq_of_orthonormal_coordinates {n : ℕ} (A B z : Point n) (a b : ℝ)
    (hAA : (inner ℝ (A) (A)) = 1) (hBB : (inner ℝ (B) (B)) = 1) (hAB : (inner ℝ (A) (B)) = 0)
    (hzA : (inner ℝ (z) (A)) = a) (hzB : (inner ℝ (z) (B)) = b)
    (hzz : (inner ℝ (z) (z)) = a^2+b^2) : z = a • A + b • B := by
  have hBA : (inner ℝ (B) (A)) = 0 := (real_inner_comm A B).trans hAB
  have hAz : (inner ℝ (A) (z)) = a := (real_inner_comm z A).trans hzA
  have hBz : (inner ℝ (B) (z)) = b := (real_inner_comm z B).trans hzB
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hAA, hBB, hAB, hBA,
    hzA, hzB, hAz, hBz, hzz]
  ring

/-- The three-anchor Gram data determine a common affine Euclidean frame. -/
lemma affine_frame_of_anchor_gram {ι : Type*} {n : ℕ}
    (y : ι → Point n) (a b : ι → ℝ) (p : Point n) (d e : Point n)
    (hdd : (inner ℝ (d) (d)) = 4) (hee : (inner ℝ (e) (e)) = 2) (hde : (inner ℝ (d) (e)) = 2)
    (hzz : ∀ i, (inner ℝ (y i-p) (y i-p)) = (a i-1)^2+(b i)^2)
    (hzd : ∀ i, (inner ℝ (y i-p) (d)) = 2*(1-a i))
    (hze : ∀ i, (inner ℝ (y i-p) (e)) = 1-a i+b i) :
    ∃ c A B : Point n, (inner ℝ (A) (A)) = 1 ∧ (inner ℝ (B) (B)) = 1 ∧
      (inner ℝ (A) (B)) = 0 ∧ ∀ i, y i = c + a i • A + b i • B := by
  let A : Point n := (-1/2 : ℝ) • d
  let B : Point n := e - (1/2 : ℝ) • d
  let c : Point n := p + (1/2 : ℝ) • d
  have hed : (inner ℝ (e) (d)) = 2 := (real_inner_comm d e).trans hde
  have hAA : (inner ℝ (A) (A)) = 1 := by
    dsimp [A]
    simp only [real_inner_smul_left, real_inner_smul_right, hdd]
    norm_num
  have hBB : (inner ℝ (B) (B)) = 1 := by
    dsimp [B]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdd, hee, hde, hed]
    norm_num
  have hAB : (inner ℝ (A) (B)) = 0 := by
    dsimp [A,B]
    simp only [inner_sub_right, real_inner_smul_left, real_inner_smul_right, hdd, hde]
    norm_num
  refine ⟨c,A,B,hAA,hBB,hAB,?_⟩
  intro i
  have hzA : (inner ℝ (y i-p) (A)) = a i-1 := by
    dsimp [A]
    rw [real_inner_smul_right, hzd]
    ring
  have hzB : (inner ℝ (y i-p) (B)) = b i := by
    dsimp [B]
    rw [inner_sub_right, real_inner_smul_right, hze, hzd]
    ring
  have hv := vector_eq_of_orthonormal_coordinates A B (y i-p) (a i-1) (b i)
    hAA hBB hAB hzA hzB (hzz i)
  calc
    y i = p + (y i-p) := by abel
    _ = p + ((a i-1) • A + b i • B) := by rw [hv]
    _ = c + a i • A + b i • B := by dsimp [c,A]; module

end GrahamSpherical

end

end OAI
