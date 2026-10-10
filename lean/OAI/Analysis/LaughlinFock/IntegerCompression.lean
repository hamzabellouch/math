import Mathlib
import OAI.Analysis.LaughlinFock.IntegerFour

namespace OAI

/-! Integer Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem planar_certificate_of_integer (D : ℕ)
    (h : ((integerCompression D).map (algebraMap ℚ ℂ)).PosSemidef) :
    (planarFourGram D * planarFourComparison certificateRows (3/10^6) D *
      planarFourGram D).PosSemidef := by
  classical
  let d : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
    Matrix.diagonal (fun r => (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) : ℂ))
  let G := (integerFourGram D).map (algebraMap ℚ ℂ)
  let Y := (integerRowsFourTrace D).map (algebraMap ℚ ℂ)
  let u : CopyLabel D → ℂ := fun r => (rationalCopyDiagonal D r.val.val : ℂ)
  let c : CopyLabel D → ℂ := fun r => (if r.val.val=1 then 2 else 0)+3/10^6
  have hd : dᴴ = d := by
    ext r s
    by_cases hrs : r=s <;> simp [d, Matrix.conjTranspose_apply, hrs, eq_comm]
  have hDD : d*d=Matrix.diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    have hu : 0 ≤ (rationalCopyDiagonal D r.val.val : ℝ) := by
      exact_mod_cast (rationalCopyDiagonal_pos D r.val.val).le
    change (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) : ℂ)*
      (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
    simp [u]
  have hc : d*Matrix.diagonal c*d = Matrix.diagonal (fun r => c r*u r) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    have hv := congrFun (congrFun hDD r) r
    simp only [d, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at hv
    rw [mul_right_comm, hv]
    exact mul_comm _ _
  have hG : planarFourGram D = d*G*d := by
    ext r s
    rw [planarFourGram_rational, rationalFourGram_integer]
    simp [d,G,Matrix.diagonal_mul,Matrix.mul_diagonal, Complex.ofReal_mul]
  have hE : (Matrix.of (fun r s => ((∑ t : Fin 8,
      planarRowFourTrace D (certificateRows t).t.val (certificateRows t).alpha r s : ℝ) : ℂ))) =
      d*Y*d := by
    ext r s
    simp only [Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, d,Y,
      Matrix.map_apply, integerRowsFourTrace, Matrix.sum_apply, map_sum, Complex.ofReal_sum,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    change ((planarRowFourTrace D t.val (rationalComparisonRow t (certificateEll t)
      (certificateAlpha t)).alpha r s : ℝ) : ℂ) = _
    rw [planarRowFourTrace_rational D t (certificateEll t) (certificateAlpha t),
      rationalFourTrace_integer]
    simp
  have hC : planarFourComparison certificateRows (3/10^6) D = Matrix.diagonal c - d*Y*d := by
    rw [planarFourComparison, hE]
    have hct : (2:ℂ) • targetCopy D + ((3/10^6:ℝ):ℂ) • (1:Matrix (CopyLabel D) (CopyLabel D) ℂ) =
        Matrix.diagonal c := by
      ext r s
      by_cases he : r=s
      · subst s
        simp [targetCopy, c, Matrix.smul_apply]
      · have hf : ¬ (r.val.val=1 ∧ s.val.val=1) := by
          intro hh
          apply he
          apply Subtype.ext
          apply Fin.ext
          omega
        simp [targetCopy, c, Matrix.smul_apply, he, hf]
    rw [← hct]
    abel
  have hM : (integerFourMiddle D).map (algebraMap ℚ ℂ) =
      Matrix.diagonal (fun r => c r*u r) - Matrix.diagonal u*Y*Matrix.diagonal u := by
    ext r s
    simp only [integerFourMiddle, Matrix.map_apply, Matrix.sub_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hrs : r=s
    · subst s
      simp only [Matrix.diagonal_apply_eq]
      dsimp [c,u,Y]
      split_ifs <;> simp
    · simp [hrs, c,u,Y]
  have hfull : planarFourGram D * planarFourComparison certificateRows (3/10^6) D *
      planarFourGram D = d*((integerCompression D).map (algebraMap ℚ ℂ))*d := by
    rw [hG, hC, integerCompression, Matrix.map_mul, Matrix.map_mul, hM]
    calc
      _ = d*(G*(d*Matrix.diagonal c*d-(d*d)*Y*(d*d))*G)*d := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = _ := by rw [hDD, hc]
  rw [hfull]
  simpa only [hd] using h.mul_mul_conjTranspose_same d

end LaughlinFock
end

end OAI
