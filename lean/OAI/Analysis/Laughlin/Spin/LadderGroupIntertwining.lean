import OAI.Analysis.Laughlin.Asymptotics.UpperSpinDynamics

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix Kronecker

theorem weight_support_diagonal_intertwining (A B z J : ℕ) (hz : 2*z+J=A+B)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hs : ∀ i n, i.1.val+i.2.val ≠ z+n.val → W i n=0)
    (x y : ℂ) (hxy : x*y=1) :
    (generalSpinMatrix A (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) ⊗ₖ
      generalSpinMatrix B (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)))*W =
        W*generalSpinMatrix J (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) := by
  rw [generalSpinMatrix_diagonal,generalSpinMatrix_diagonal,generalSpinMatrix_diagonal,
    Matrix.diagonal_kronecker_diagonal]
  ext i n
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi : i.1.val+i.2.val=z+n.val
  · have he : A-i.1.val+(B-i.2.val)=z+(J-n.val) := by
      have h1 := i.1.isLt
      have h2 := i.2.isLt
      have hn := n.isLt
      omega
    have hf : (y^i.1.val*x^(A-i.1.val))*(y^i.2.val*x^(B-i.2.val)) = y^n.val*x^(J-n.val) := by
      calc
        _ = y^(i.1.val+i.2.val)*x^(A-i.1.val+(B-i.2.val)) := by simp only [pow_add]; ring
        _ = (x*y)^z*(y^n.val*x^(J-n.val)) := by rw [hi,he]; simp only [pow_add,mul_pow]; ring
        _ = _ := by rw [hxy,one_pow,one_mul]
    rw [hf]
    ring
  · rw [hs i n hi]
    simp

theorem ladder_intertwiner_SU2 (A B z J : ℕ) (hz : 2*z+J=A+B)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hs : ∀ i n, i.1.val+i.2.val ≠ z+n.val → W i n=0)
    (hr : totalRaiseComplex A B*W=W*spinRaiseComplex J)
    (hl : (totalRaiseComplex A B)ᵀ*W=W*(spinRaiseComplex J)ᵀ)
    (g : SourceSU2) :
    (sourceSpinRepresentation A g ⊗ₖ sourceSpinRepresentation B g)*W =
      W*sourceSpinRepresentation J g := by
  let P : Matrix (Fin 2) (Fin 2) ℂ → Prop := fun M =>
    (generalSpinMatrix A M ⊗ₖ generalSpinMatrix B M)*W=W*generalSpinMatrix J M
  have h : P g.val := by
    apply Matrix.diagonal_transvection_induction P g.val
    · intro D hD
      have hxy : D 0*D 1=1 := by
        simpa [Matrix.det_diagonal,Fin.prod_univ_two] using hD.trans g.property.2
      have he : D=(fun i : Fin 2 => if i=0 then D 0 else D 1) := by
        funext i
        fin_cases i <;> simp
      change (generalSpinMatrix A (Matrix.diagonal D) ⊗ₖ
        generalSpinMatrix B (Matrix.diagonal D))*W=W*generalSpinMatrix J (Matrix.diagonal D)
      rw [he]
      exact weight_support_diagonal_intertwining A B z J hz W hs _ _ hxy
    · rintro ⟨i,j,hij,c⟩
      change (generalSpinMatrix A (Matrix.transvection i j c) ⊗ₖ
        generalSpinMatrix B (Matrix.transvection i j c))*W=W*generalSpinMatrix J (Matrix.transvection i j c)
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact raising_intertwiner_upper A B J W hr c
      · exact lowering_intertwiner_lower A B J W hl c
      · exact False.elim (hij rfl)
    · intro M L hM hL
      change (generalSpinMatrix A (M*L) ⊗ₖ generalSpinMatrix B (M*L))*W=W*generalSpinMatrix J (M*L)
      rw [generalSpinMatrix_mul,generalSpinMatrix_mul,generalSpinMatrix_mul,Matrix.mul_kronecker_mul]
      change (generalSpinMatrix A M ⊗ₖ generalSpinMatrix B M)*
        (generalSpinMatrix A L ⊗ₖ generalSpinMatrix B L)*W=W*(generalSpinMatrix J M*generalSpinMatrix J L)
      rw [Matrix.mul_assoc,hL,← Matrix.mul_assoc,hM,Matrix.mul_assoc]
  exact h

end Laughlin.Rotation

end OAI
