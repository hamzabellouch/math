import OAI.MathematicalPhysics.Heisenberg.SpinMatrixTrace

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma pow_intertwines (A : Matrix m m ℝ) (B : Matrix n n ℝ) (V : Matrix m n ℝ)
    (h : A*V=V*B) (k : ℕ) : A^k*V=V*B^k := by
  induction k with
  | zero=> simp
  | succ k ih=>
    rw [pow_succ',Matrix.mul_assoc,ih,←Matrix.mul_assoc,h,Matrix.mul_assoc,←pow_succ']

theorem exp_intertwines (A : Matrix m m ℝ) (B : Matrix n n ℝ) (V : Matrix m n ℝ)
    (h : A*V=V*B) : NormedSpace.exp A*V=V*NormedSpace.exp B := by
  let L:=mulRightLinearMap m ℝ V
  let R:=mulLeftLinearMap n ℝ V
  have hL : Continuous L:=L.continuous_of_finiteDimensional
  have hR : Continuous R:=R.continuous_of_finiteDimensional
  have ha:=(NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) A).map L.toAddMonoidHom hL
  have hb:=(NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) B).map R.toAddMonoidHom hR
  have he : (fun k : ℕ=>L ((k.factorial:ℝ)⁻¹ • A^k))=
      (fun k : ℕ=>R ((k.factorial:ℝ)⁻¹ • B^k)) := by
    funext k
    change ((k.factorial:ℝ)⁻¹ • A^k)*V=V*((k.factorial:ℝ)⁻¹ • B^k)
    rw [Matrix.smul_mul,Matrix.mul_smul,pow_intertwines A B V h]
  change HasSum (fun k : ℕ=>L ((k.factorial:ℝ)⁻¹ • A^k)) (NormedSpace.exp A*V) at ha
  change HasSum (fun k : ℕ=>R ((k.factorial:ℝ)⁻¹ • B^k)) (V*NormedSpace.exp B) at hb
  rw [he] at ha
  exact ha.unique hb

end Heisenberg.TensorMatrix
end
end

end OAI
