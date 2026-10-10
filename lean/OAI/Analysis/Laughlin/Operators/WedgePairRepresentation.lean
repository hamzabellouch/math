import OAI.Analysis.Laughlin.Operators.WedgePairRotation

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem real_matrix_inverse_complex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (A : Matrix I J ℝ) (B : Matrix J I ℝ) (h : A*B=1) :
    A.map Complex.ofReal * B.map Complex.ofReal = 1 := by
  ext i j
  have he := congrArg Complex.ofReal (congrFun (congrFun h i) j)
  simpa only [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum,Complex.ofReal_mul,
    Matrix.one_apply,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using he

theorem real_matrix_adjoint {I J : Type*} (A : Matrix I J ℝ) :
    (A.map Complex.ofReal)ᴴ = Aᵀ.map Complex.ofReal := by
  ext i j
  simp [Matrix.conjTranspose_apply,Matrix.transpose_apply]

noncomputable def complexPairBasis (Q : ℕ) := (pairCoupledBasis Q).map Complex.ofReal

theorem complexPairBasis_isometry (Q : ℕ) :
    (complexPairBasis Q)ᴴ * complexPairBasis Q = 1 := by
  rw [complexPairBasis,real_matrix_adjoint]
  exact real_matrix_inverse_complex _ _ (pairCoupledBasis_isometry Q)

theorem complexPairBasis_complete (Q : ℕ) :
    complexPairBasis Q * (complexPairBasis Q)ᴴ = 1 := by
  rw [complexPairBasis,real_matrix_adjoint]
  exact real_matrix_inverse_complex _ _ (pairCoupledBasis_complete Q)

noncomputable def pairBasisAction (Q : ℕ) (g : SourceSU2) :
    Matrix (PairCoupledIndex Q) (PairCoupledIndex Q) ℂ :=
  Matrix.blockDiagonal' (fun r : OddPairLabel Q =>
    sourceSpinRepresentation (genericCoupledWeight Q Q (oddPairDeficit r)) g)

theorem wedgePairMatrix_basis (Q : ℕ) (g : SourceSU2) :
    wedgePairMatrix Q g * complexPairBasis Q = complexPairBasis Q * pairBasisAction Q g := by
  ext i s
  have hb : (complexPairBasis Q * pairBasisAction Q g) i s =
      ∑ n, complexPairBasis Q i ⟨s.1,n⟩ *
        sourceSpinRepresentation (genericCoupledWeight Q Q (oddPairDeficit s.1)) g n s.2 := by
    rw [Matrix.mul_apply,Fintype.sum_sigma,Finset.sum_eq_single s.1]
    · cases s; simp only [pairBasisAction,Matrix.blockDiagonal'_apply_eq]
    · intro r hr hrs
      simp only [pairBasisAction,Matrix.blockDiagonal'_apply_ne _ _ _ hrs,mul_zero,Finset.sum_const_zero]
    · simp
  rw [hb]
  exact congrFun (congrFun (pairCoupledInclusion_SU2 Q (oddPairDeficit s.1)
    (oddPairDeficit_le s.1) (oddPairDeficit_odd s.1) g) i) s.2

theorem wedgePairMatrix_factor (Q : ℕ) (g : SourceSU2) :
    wedgePairMatrix Q g = complexPairBasis Q * pairBasisAction Q g * (complexPairBasis Q)ᴴ := by
  rw [← wedgePairMatrix_basis,Matrix.mul_assoc,complexPairBasis_complete,Matrix.mul_one]

theorem pairBasisAction_one (Q : ℕ) : pairBasisAction Q 1=1 := by
  simp only [pairBasisAction,map_one]
  exact Matrix.blockDiagonal'_one

theorem pairBasisAction_mul (Q : ℕ) (g h : SourceSU2) :
    pairBasisAction Q (g*h) = pairBasisAction Q g * pairBasisAction Q h := by
  simp only [pairBasisAction,map_mul,Matrix.blockDiagonal'_mul]

theorem wedgePairMatrix_one (Q : ℕ) : wedgePairMatrix Q 1=1 := by
  rw [wedgePairMatrix_factor,pairBasisAction_one,Matrix.mul_one,complexPairBasis_complete]

theorem wedgePairMatrix_mul (Q : ℕ) (g h : SourceSU2) :
    wedgePairMatrix Q (g*h) = wedgePairMatrix Q g * wedgePairMatrix Q h := by
  rw [wedgePairMatrix_factor,wedgePairMatrix_factor Q g,wedgePairMatrix_factor Q h,pairBasisAction_mul]
  calc
    _ = complexPairBasis Q * pairBasisAction Q g *
      ((complexPairBasis Q)ᴴ * complexPairBasis Q) * pairBasisAction Q h * (complexPairBasis Q)ᴴ := by
      rw [complexPairBasis_isometry,Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

noncomputable def wedgePairRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (WedgePairIndex Q) (WedgePairIndex Q) ℂ where
  toFun := wedgePairMatrix Q
  map_one' := wedgePairMatrix_one Q
  map_mul' := wedgePairMatrix_mul Q

theorem wedgePairRepresentation_continuous (Q : ℕ) (i j : WedgePairIndex Q) :
    Continuous (fun g => wedgePairRepresentation Q g i j) :=
  ((sourceSpinRepresentation_continuous Q i.val.1 j.val.1).mul
    (sourceSpinRepresentation_continuous Q i.val.2 j.val.2)).sub
    ((sourceSpinRepresentation_continuous Q i.val.1 j.val.2).mul
      (sourceSpinRepresentation_continuous Q i.val.2 j.val.1))

theorem wedgePairRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    wedgePairRepresentation Q g⁻¹ = (wedgePairRepresentation Q g)ᴴ := by
  ext i j
  simp only [wedgePairRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,wedgePairMatrix,
    Matrix.conjTranspose_apply,sourceSpinRepresentation_inv,star_sub,star_mul]
  ring

end Laughlin.Spin

end OAI
