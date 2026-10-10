import OAI.InformationTheory.AmplitudeDamping.Pinching

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

def zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    Matrix (ι ⊕ ν) (κ ⊕ μ) ℂ := Matrix.fromBlocks A B C 0

def gram (A : Matrix ι κ ℂ) : Matrix ι ι ℂ := A * Aᴴ

def mass (A : Matrix ι κ ℂ) : ℝ := (gram A).trace.re

def logGram (A : Matrix ι κ ℂ) : ℝ := Real.log ‖(1+gram A).det‖

omit [DecidableEq ι] [DecidableEq κ] in
theorem mass_nonneg (A : Matrix ι κ ℂ) : 0 ≤ mass A :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose A).trace_nonneg).1

omit [DecidableEq κ] in
theorem one_add_gram_posDef (A : Matrix ι κ ℂ) : (1 + gram A).PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose A)

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] in
theorem gram_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    gram (zeroBlock A B C) = Matrix.fromBlocks (gram A + gram B) (A*Cᴴ) (C*Aᴴ) (gram C) := by
  simp [gram, zeroBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] in
theorem mass_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    mass (zeroBlock A B C) = mass A + mass B + mass C := by
  simp [mass, gram_zeroBlock, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem resolvent_complement (C : Matrix ν κ ℂ) :
    1 - Cᴴ * (1 + C*Cᴴ)⁻¹ * C = (1+Cᴴ*C)⁻¹ := by
  have hQ := (one_add_gram_posDef C).isUnit
  have hQQ : (1+C*Cᴴ)*(1+C*Cᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hQ)
  apply (Matrix.inv_eq_right_inv ?_).symm
  calc
    (1+Cᴴ*C) * (1-Cᴴ*(1+C*Cᴴ)⁻¹*C) =
      1+Cᴴ*C-Cᴴ*((1+C*Cᴴ)*(1+C*Cᴴ)⁻¹)*C := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hQQ]; simp

omit [DecidableEq μ] in
theorem det_one_add_gram_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ)
    (C : Matrix ν κ ℂ) :
    (1+gram (zeroBlock A B C)).det = (1+gram C).det *
      (1+gram B+A*(1+Cᴴ*C)⁻¹*Aᴴ).det := by
  have he : 1+gram (zeroBlock A B C) = Matrix.fromBlocks
      (1+gram A+gram B) (A*Cᴴ) (C*Aᴴ) (1+gram C) := by
    rw [gram_zeroBlock, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp [add_assoc]
  rw [he]
  let := (one_add_gram_posDef C).isUnit.invertible
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  rw [← resolvent_complement C]
  dsimp only [gram]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

omit [DecidableEq μ] in
theorem logGram_zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ)
    (C : Matrix ν κ ℂ) :
    logGram (zeroBlock A B C) = logGram B + logGram C +
      blockLogDet A (1+gram B) (1+Cᴴ*C) := by
  have hC : ‖(1+gram C).det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (one_add_gram_posDef C).isUnit))
  have hE : (1+Cᴴ*C).PosDef := by simpa [gram] using one_add_gram_posDef Cᴴ
  have hS := (one_add_gram_posDef B).add_posSemidef (hE.inv.posSemidef.mul_mul_conjTranspose_same A)
  have hnS : ‖(1+gram B+A*(1+Cᴴ*C)⁻¹*Aᴴ).det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit))
  simp only [logGram, det_one_add_gram_zeroBlock, norm_mul, Real.log_mul hC hnS, blockLogDet]
  ring

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem gram_sqrt_smul {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ) :
    gram (Real.sqrt r • A) = r • gram A := by
  simp only [gram, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hr]

omit [DecidableEq κ] in
theorem logDetShift_eq_logGram {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ) :
    logDetShift r (gram A) = logGram (Real.sqrt r • A) := by
  simp only [logDetShift, logGram, gram_sqrt_smul hr]

omit [DecidableEq μ] in
theorem logDetShift_zeroBlock {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ)
    (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    logDetShift r (gram (zeroBlock A B C)) = logDetShift r (gram B) +
      logDetShift r (gram C) + blockLogDet (Real.sqrt r • A) (1+r • gram B) (1+r • (Cᴴ*C)) := by
  rw [logDetShift_eq_logGram hr, logDetShift_eq_logGram hr, logDetShift_eq_logGram hr]
  have hb : Real.sqrt r • zeroBlock A B C =
      zeroBlock (Real.sqrt r • A) (Real.sqrt r • B) (Real.sqrt r • C) := by
    simp [zeroBlock, Matrix.fromBlocks_smul]
  rw [hb, logGram_zeroBlock, gram_sqrt_smul hr]
  congr 2
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt hr]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

theorem log_norm_det_diagonal_real (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    Real.log ‖(Matrix.diagonal (fun i ↦ (d i : ℂ))).det‖ = ∑ i, Real.log (d i) := by
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd _)]
  exact Real.log_prod (fun i _ ↦ (hd i).ne')

theorem blockLogDet_diagonal_real (z d e : ι → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i) :
    blockLogDet (Matrix.diagonal (fun i ↦ (z i : ℂ)))
      (Matrix.diagonal (fun i ↦ (d i : ℂ))) (Matrix.diagonal (fun i ↦ (e i : ℂ))) =
      ∑ i, Real.log (1+(z i)^2/(d i*e i)) := by
  have hinv : (Matrix.diagonal (fun i ↦ (e i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i ↦ ((e i)⁻¹ : ℂ)) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have heq : (fun i ↦ (e i : ℂ) * ((e i)⁻¹ : ℂ)) = fun _ ↦ (1 : ℂ) := by
      ext i
      simp [Complex.ofReal_ne_zero.mpr (he i).ne']
    rw [heq, Matrix.diagonal_one]
  have hmat : Matrix.diagonal (fun i ↦ (d i : ℂ)) +
      Matrix.diagonal (fun i ↦ (z i : ℂ)) *
      (Matrix.diagonal (fun i ↦ (e i : ℂ)))⁻¹ *
      (Matrix.diagonal (fun i ↦ (z i : ℂ)))ᴴ =
      Matrix.diagonal (fun i ↦ ((d i+(z i)^2/e i : ℝ) : ℂ)) := by
    rw [hinv, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1
    ext i
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
  have hp (i : ι) : 0 < d i+(z i)^2/e i := add_pos_of_pos_of_nonneg (hd i)
    (div_nonneg (sq_nonneg _) (he i).le)
  unfold blockLogDet
  rw [hmat, log_norm_det_diagonal_real _ hp, log_norm_det_diagonal_real _ hd, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.log_div (hp i).ne' (hd i).ne']
  congr 1
  field_simp [(hd i).ne', (he i).ne']

theorem logDetShift_diagonal_real (r : ℝ) (d : ι → ℝ) (hr : 0 ≤ r) (hd : ∀ i, 0 ≤ d i) :
    logDetShift r (Matrix.diagonal (fun i ↦ (d i : ℂ))) = ∑ i, Real.log (1+r*d i) := by
  have he : (1 : Matrix ι ι ℂ)+r • Matrix.diagonal (fun i ↦ (d i : ℂ)) =
      Matrix.diagonal (fun i ↦ ((1+r*d i : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    ext i
    simp [Complex.real_smul]
  rw [logDetShift, he, log_norm_det_diagonal_real]
  intro i
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hd i))

end GAD

end

end OAI
