import OAI.MathematicalPhysics.Heisenberg.RectangularExp

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma diagonal_function_intertwines (a : m → ℝ) (b : n → ℝ) (V : Matrix m n ℝ)
    (h : Matrix.diagonal a*V=V*Matrix.diagonal b) (f : ℝ → ℝ) :
    Matrix.diagonal (f ∘ a)*V=V*Matrix.diagonal (f ∘ b) := by
  ext i j
  have he:=congrFun (congrFun h i) j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he ⊢
  by_cases hv : V i j=0
  · simp [hv]
  · have hab : a i=b j:=mul_right_cancel₀ hv (he.trans (mul_comm _ _))
    simp only [Function.comp_apply,hab,mul_comm]

omit [Fintype m] in
lemma diagonal_fintype_sum {I : Type*} [Fintype I] (f : I → m → ℝ) :
    (∑ i,Matrix.diagonal (f i))=Matrix.diagonal (fun j=>∑ i,f i j) := by
  ext a b
  by_cases h : a=b
  · subst b; simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply,Matrix.diagonal_apply_ne _ h]

theorem trace_exp_compression (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (V : Matrix m n ℝ) (hV : V.transpose*V=1) (hAB : A*V=V*B)
    (D : Matrix m m ℝ) (E : Matrix n n ℝ) (hDE : D*V=V*E) :
    Matrix.trace (V*V.transpose*NormedSpace.exp A*D)=Matrix.trace (NormedSpace.exp B*E) := by
  rw [Matrix.mul_assoc,Matrix.mul_assoc,Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hDE,←Matrix.mul_assoc (NormedSpace.exp A) V E,exp_intertwines A B V hAB]
  simp only [←Matrix.mul_assoc,hV,Matrix.one_mul]

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

def physicalMagnetization (ℓ : ℕ) (k : X → Level ℓ) : ℝ :=
  ∑ x,((k x:ℝ)-(ℓ:ℝ)/2)

def configMagnetization (ℓ : ℕ) (A : X → Config ℓ) : ℝ :=
  ∑ x,((A x).card-(ℓ:ℝ)/2)

lemma total_diagonal_intertwines (ℓ : ℕ) :
    Matrix.diagonal (configMagnetization (X:=X) ℓ)*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*Matrix.diagonal (physicalMagnetization (X:=X) ℓ) := by
  have hh:=congrArg (fun f : X → Matrix (X → Config ℓ) (X → Level ℓ) ℝ=>∑ x,f x)
    (funext (diagonal_intertwines (X:=X) ℓ))
  simp only [SpinSlots.diagonalZ,physicalZ,local_diagonal,←Matrix.sum_mul,←Matrix.mul_sum,
    diagonal_fintype_sum] at hh
  exact hh

omit [DecidableEq X] in
lemma color_config_mag (ℓ : ℕ) (A : X → Config ℓ) :
    SlotColor.magnetization ((configEquiv ℓ).symm A)=configMagnetization ℓ A := by
  unfold SlotColor.magnetization configMagnetization
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have he (a : Fin ℓ) : (if ((configEquiv ℓ).symm A) (x,a) then (1:ℝ)/2 else -1/2)=
      (if a∈A x then (1:ℝ) else 0)-1/2 := by
    change (if decide (a∈A x) then (1:ℝ)/2 else -1/2)=_
    by_cases ha : a∈A x <;> simp [ha] <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp [div_eq_mul_inv]

end Heisenberg.SlotTensor
end

end OAI
