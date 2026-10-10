import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder CStarAlgebra BigOperators WithCStarModule
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

lemma matrix_norm_le_sum {m n : Type*} [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum,Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

lemma two_isometries_of_near_gram (x : Fin 2 → A)
    (h : ∀ i j, ‖star (x i)*x j - (if i=j then 1 else 0)‖ ≤ (1/16:ℝ)) :
    ∃ s t : A, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin 2) (Fin 2) A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin 2) (Fin 2) A) :=
    CStarAlgebra.instNonnegSpectrumClass
  let X : CStarMatrix (Fin 2) (Fin 2) A :=
    CStarMatrix.ofMatrix fun i j => if i=0 then x j else 0
  let Q := star X * X
  have hQ (i j : Fin 2) : Q i j = star (x i)*x j := by
    change (∑ k : Fin 2, star (X k i) * X k j) = star (x i) * x j
    rw [Fin.sum_univ_two]
    change star (x i) * x j + star (0 : A) * 0 = star (x i) * x j
    simp
  have hb : ‖1-Q‖ ≤ (1/4:ℝ) := by
    apply (matrix_norm_le_sum (1-Q)).trans
    calc
      _ ≤ ∑ _ : Fin 2, ∑ _ : Fin 2, (1/16:ℝ) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro i _
        simpa only [CStarMatrix.sub_apply,CStarMatrix.one_apply,hQ,norm_sub_rev] using h i j
      _ = 1/4 := by norm_num
  have hu : IsUnit Q := by
    have hu := (Units.oneSub (1-Q) (hb.trans_lt (by norm_num))).isUnit
    simpa only [Units.val_oneSub,sub_sub_cancel] using hu
  have hpos : IsStrictlyPositive Q := hu.isStrictlyPositive (star_mul_self_nonneg X)
  let L := Q ^ (-(1/2):ℝ)
  have hL : star L = L := (CFC.rpow_nonneg (a:=Q) (y:=(-(1/2):ℝ))).isSelfAdjoint.star_eq
  let Y := X * L
  have hYY : star Y * Y = 1 := by
    calc
      _ = L * Q * L := by simp only [Y,star_mul,hL,Q,mul_assoc]
      _ = 1 := CFC.conjugate_rpow_neg_one_half Q hpos
  have hzero (j : Fin 2) : Y 1 j = 0 := by
    change (∑ k : Fin 2, X 1 k * L k j) = 0
    rw [Fin.sum_univ_two]
    change (0 : A) * L 0 j + 0 * L 1 j = 0
    simp
  have he (i j : Fin 2) : star (Y 0 i)*Y 0 j = if i=j then 1 else 0 := by
    have hh := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M i j) hYY
    simpa [CStarMatrix.mul_apply,CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply,Fin.sum_univ_two,hzero,CStarMatrix.one_apply] using hh
  exact ⟨Y 0 0,Y 0 1,by simpa using he 0 0,by simpa using he 1 1,by simpa using he 0 1⟩


end KaplanskyConsequences

end

end OAI
