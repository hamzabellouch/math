import Mathlib
import OAI.Geometry.PrescribedRicci.TraceCauchySchwarz

namespace OAI

/-! Chern Lu Gradient. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
lemma tracePair_sum (B K : Matrix n n ℂ) (W : m → Matrix n n ℂ) (v : m → ℂ) :
    (B*(∑ i, v i • W i)ᴴ*K*(∑ j, v j • W j)).trace =
      ∑ i, ∑ j, star (v i)*v j*(B*(W i)ᴴ*K*W j).trace := by
  simp only [conjTranspose_sum,conjTranspose_smul,Matrix.sum_mul,
    Matrix.mul_smul,Matrix.smul_mul,trace_sum,trace_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq n] [DecidableEq m] in
lemma trace_sum_smul (B : Matrix n n ℂ) (W : m → Matrix n n ℂ) (v : m → ℂ) :
    (B*(∑ i, v i • W i)).trace = ∑ i, v i*(B*W i).trace := by
  simp only [Matrix.mul_sum,Matrix.mul_smul,trace_sum,trace_smul,smul_eq_mul]

omit [DecidableEq m] in
lemma trace_schur_posSemidef (B G : Matrix n n ℂ) (hB : B.PosSemidef)
    (hG : G.PosDef) (W : m → Matrix n n ℂ) :
    Matrix.PosSemidef (fun i j => ((B*G).trace.re : ℂ)*(B*(W i)ᴴ*G⁻¹*W j).trace -
      star (B*W i).trace*(B*W j).trace : Matrix m m ℂ) := by
  let S := (B*G).trace.re
  let N : Matrix m m ℂ := fun i j => (S:ℂ)*(B*(W i)ᴴ*G⁻¹*W j).trace -
    star (B*W i).trace*(B*W j).trace
  have hs (i j : m) : star (B*(W j)ᴴ*G⁻¹*W i).trace = (B*(W i)ᴴ*G⁻¹*W j).trace :=
    (tracePairCore B G⁻¹ hB hG.inv.posSemidef).conj_inner_symm _ _
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    change star (N j i) = N i j
    dsimp only [N]
    rw [star_sub,star_mul,star_mul,star_star,hs]
    simp only [Complex.star_def,Complex.conj_ofReal]
    ring
  · intro v
    let C := ∑ i, v i • W i
    have he : star v ⬝ᵥ (N *ᵥ v) = (S:ℂ)*(B*Cᴴ*G⁻¹*C).trace -
        star (B*C).trace*(B*C).trace := by
      dsimp only [C]
      rw [tracePair_sum,trace_sum_smul]
      simp only [dotProduct,mulVec,Pi.star_apply,N,Finset.mul_sum,Finset.sum_mul,
        Finset.sum_sub_distrib,mul_sub,sub_mul,star_sum,star_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    change 0 ≤ star v ⬝ᵥ (N *ᵥ v)
    rw [he]
    have hq := (tracePairCore B G⁻¹ hB hG.inv.posSemidef).conj_inner_symm C C
    have hqi : (B*Cᴴ*G⁻¹*C).trace.im = 0 := by
      have hi := congrArg Complex.im hq
      simp only [Complex.conj_im] at hi
      change -(B*Cᴴ*G⁻¹*C).trace.im = (B*Cᴴ*G⁻¹*C).trace.im at hi
      linarith
    have hCS := trace_cauchySchwarz B G C hB hG
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        Complex.star_def,Complex.conj_re,Complex.conj_im]
      rw [Complex.sq_norm,Complex.normSq_apply] at hCS
      dsimp only [S]
      nlinarith
    · simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
        hqi,mul_zero,Complex.star_def,Complex.conj_re,Complex.conj_im]
      ring

lemma chernLu_gradient_bound (B G : Matrix n n ℂ) (hB : B.PosSemidef)
    (hG : G.PosDef) (W : n → Matrix n n ℂ) :
    (∑ a, ∑ b, B a b*star (B*W b).trace*(B*W a).trace).re ≤
      (B*G).trace.re * (∑ a, ∑ b, B a b*(B*(W b)ᴴ*G⁻¹*W a).trace).re := by
  have hn := EllipticKernel.trace_mul_nonneg hB (trace_schur_posSemidef B G hB hG W)
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply] at hn
  have he : (∑ a, ∑ b, B a b *
      (((B*G).trace.re:ℂ)*(B*(W b)ᴴ*G⁻¹*W a).trace-star (B*W b).trace*(B*W a).trace)) =
      ((B*G).trace.re:ℂ)*(∑ a, ∑ b, B a b*(B*(W b)ᴴ*G⁻¹*W a).trace) -
        (∑ a, ∑ b, B a b*star (B*W b).trace*(B*W a).trace) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  change 0 ≤ (∑ a, ∑ b, B a b *
      (((B*G).trace.re:ℂ)*(B*(W b)ᴴ*G⁻¹*W a).trace-star (B*W b).trace*(B*W a).trace)).re at hn
  rw [he,Complex.sub_re,Complex.re_ofReal_mul] at hn
  linarith

end MongeAmpere

end

end OAI
