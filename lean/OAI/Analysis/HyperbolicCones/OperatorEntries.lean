import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem operatorNorm_eq_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    operatorNorm A = ‖A‖ := rfl

theorem operatorNorm_smul {m n : ℕ} (s : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    operatorNorm (s • A) = |s| * operatorNorm A := by
  simp only [operatorNorm_eq_norm, norm_smul, Real.norm_eq_abs]

theorem operatorNorm_continuous {m n : ℕ} :
    Continuous (operatorNorm (m := m) (n := n)) := by
  simpa only [operatorNorm_eq_norm] using!
    (continuous_norm : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => ‖A‖))

theorem abs_entry_le_operatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : |A i j| ≤ operatorNorm A := by
  let f := A.toEuclideanLin.toContinuousLinearMap
  have he : f (PiLp.single 2 j 1) i = A i j := by
    simp [f, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_single]
  have h₁ := PiLp.norm_apply_le (f (PiLp.single 2 j 1)) i
  have h₂ := f.unit_le_opNorm (PiLp.single 2 j 1)
    (by rw [PiLp.norm_single]; norm_num : ‖(PiLp.single 2 j (1 : ℝ) : Vec n)‖ ≤ 1)
  simpa only [he, Real.norm_eq_abs] using! h₁.trans h₂

theorem entry_sq_le_operatorNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : (A i j) ^ 2 ≤ operatorNorm A ^ 2 := by
  have h := abs_entry_le_operatorNorm A i j
  have hn : 0 ≤ operatorNorm A := norm_nonneg _
  nlinarith [sq_abs (A i j), abs_nonneg (A i j)]

end Paper256

end

end OAI
