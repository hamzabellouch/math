import Mathlib
import OAI.Analysis.Commutator.KaplanskyDensity
import OAI.Analysis.Commutator.MatrixAlgebraDensity

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def offDiagonal (a : H →L[ℂ] H) : SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2) :=
  matrixUnit (Fin 2) 0 1*diagonal (H:=H) (Fin 2) a+
    matrixUnit (Fin 2) 1 0*diagonal (H:=H) (Fin 2) (star a)

@[simp] lemma offDiagonal_zero (a : H →L[ℂ] H) (x : SumSpace (H:=H) (Fin 2)) :
    offDiagonal a x 0=a (x 1) := by
  simp [offDiagonal,mul_apply_eq_comp,matrixUnit_apply,single_apply]

@[simp] lemma offDiagonal_one (a : H →L[ℂ] H) (x : SumSpace (H:=H) (Fin 2)) :
    offDiagonal a x 1=star a (x 0) := by
  simp [offDiagonal,mul_apply_eq_comp,matrixUnit_apply,single_apply]

lemma offDiagonal_selfAdjoint (a : H →L[ℂ] H) : IsSelfAdjoint (offDiagonal a) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [ContinuousLinearMap.coe_coe,PiLp.inner_apply,Fin.sum_univ_two,
    offDiagonal_zero,offDiagonal_one,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  exact add_comm _ _

lemma offDiagonal_norm_le {a : H →L[ℂ] H} (ha : ‖a‖≤1) : ‖offDiagonal a‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two,offDiagonal_zero,offDiagonal_one]
  have h₀ := contraction_apply ha (x 1)
  have h₁ := contraction_apply (a:=star a) (by simpa only [norm_star] using ha) (x 0)
  nlinarith [norm_nonneg (a (x 1)),norm_nonneg (star a (x 0)),norm_nonneg (x 0),norm_nonneg (x 1)]

lemma entry_offDiagonal (a : H →L[ℂ] H) (i j : Fin 2) :
    entry (Fin 2) (offDiagonal a) i j=if i=0 ∧ j=1 then a else if i=1 ∧ j=0 then star a else 0 := by
  ext x
  fin_cases i <;> fin_cases j <;>
    simp [entry_apply,single_apply]

lemma star_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) {a : H →L[ℂ] H}
    (ha : a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    star a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  let B := StarSubalgebra.centralizer ℂ ((StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))) : Set (H →L[ℂ] H))
  have he : (B : Set (H →L[ℂ] H))=Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    simp only [B,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]
  have hm : a∈B := by
    change a∈(B : Set (H →L[ℂ] H))
    rw [he]
    exact ha
  rw [←he]
  exact B.star_mem' hm

lemma offDiagonal_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))] {a : H →L[ℂ] H}
    (ha : a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    offDiagonal a∈Set.centralizer (Set.centralizer (fullMatrixAlgebra (Fin 2) S :
      Set (SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2)))) := by
  apply bicommutant_fullMatrix_of_entries (Fin 2) S 0
  intro i j
  rw [entry_offDiagonal]
  split_ifs
  · exact ha
  · exact star_bicommutant S ha
  · intro T _
    simp

omit [CompleteSpace H] in
lemma single_norm (i : Fin 2) (x : H) : ‖single (Fin 2) i x‖=‖x‖ := by
  have he : single (Fin 2) i x=PiLp.single 2 i x := by
    ext j
    simp [single_apply,PiLp.single_apply]
  rw [he,PiLp.norm_single]

lemma entry_norm_le (T : SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2)) (i j : Fin 2) :
    ‖entry (Fin 2) T i j‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    _≤‖T (single (Fin 2) j x)‖ := PiLp.norm_apply_le _ _
    _≤‖T‖*‖single (Fin 2) j x‖ := T.le_opNorm _
    _=‖T‖*‖x‖ := by rw [single_norm]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem contraction_finite_approx
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ ‖a‖≤1 ∧ ∀ i, ‖a (x i)-T (x i)‖<ε := by
  let : IsClosed (S : Set (H →L[ℂ] H)) := hS
  obtain ⟨A,hA,_,hnA,he⟩ := selfAdjoint_contraction_finite_approx ι
    (fullMatrixAlgebra (Fin 2) S) (fullMatrixAlgebra_closed (Fin 2) S)
    (offDiagonal_bicommutant S hT) (offDiagonal_selfAdjoint T) (offDiagonal_norm_le hnT)
    (fun i => single (Fin 2) 1 (x i)) ε hε
  refine ⟨entry (Fin 2) A 0 1,(mem_fullMatrixAlgebra_iff (Fin 2) S A).mp hA 0 1,
    (entry_norm_le A 0 1).trans hnA,?_⟩
  intro i
  have h := (PiLp.norm_apply_le
    (A (single (Fin 2) 1 (x i))-offDiagonal T (single (Fin 2) 1 (x i))) 0).trans_lt (he i)
  simpa only [entry_apply,PiLp.sub_apply,offDiagonal_zero,single_apply,ite_true] using h

end Kadison.Kaplansky

end

end
end

end OAI
