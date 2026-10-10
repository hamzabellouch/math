import OAI.Analysis.Triangular.Construction.ActualInput

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma actualTail_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+Coperator (actualFiniteError 1 z hz hzB)-
      Aoperator (actualFiniteError 0 z hz hzB)+tailTarget z hz hzB+
      CallOperator (finiteApprox 1 (actualParameter z))-AallOperator (finiteApprox 0 (actualParameter z))+
      (3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+Coperator (actualFiniteError 0 z hz hzB)-
      Aoperator (actualFiniteError 1 z hz hzB)+
      CallOperator (finiteApprox 0 (actualParameter z))-AallOperator (finiteApprox 1 (actualParameter z))-
      (3/500:ℝ) • tailFixedColumn 22 := by
  have hp := correctionTail_equation 0 (finiteResidual z) (approximationTailResidual 0 z hz hzB)
  have hm := correctionTail_equation 1 (finiteResidual z) (approximationTailResidual 1 z hz hzB)
  change actualTailSplit 0 z hz hzB=Doperator (actualTailSplit 0 z hz hzB)+
    (Coperator-Aoperator) (actualFiniteSplit 0 z hz hzB)+approximationTailResidual 0 z hz hzB at hp
  change actualTailSplit 1 z hz hzB=(-Doperator) (actualTailSplit 1 z hz hzB)+
    (-Coperator-Aoperator) (actualFiniteSplit 1 z hz hzB)+approximationTailResidual 1 z hz hzB at hm
  constructor <;> ext i
  all_goals
    have hp' := congrArg (fun u : TailCoefficients => u i) hp
    have hm' := congrArg (fun u : TailCoefficients => u i) hm
    simp only [actualFiniteError,actualTail,approximationTailResidual,
      Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
      map_smul,map_add,map_sub,map_neg,sub_apply,neg_apply,
      lp.coeFn_add,lp.coeFn_sub,lp.coeFn_neg,lp.coeFn_smul,
      Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hp' hm' ⊢
    linarith
lemma CallOperator_extend (u : FiniteCoefficients) :
    CallOperator (extendFiniteError u)=Coperator u := by
  ext p
  unfold CallOperator Coperator
  erw [operator_apply,operator_apply,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, (if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)*CallKernel p i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 1
lemma AallOperator_extend (u : FiniteCoefficients) :
    AallOperator (extendFiniteError u)=Aoperator u := by
  ext p
  unfold AallOperator Aoperator
  erw [operator_apply,operator_apply,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, (if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)*AallKernel p i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 1
  unfold AallKernel Akernel
  congr 1 <;> apply Fin.ext <;> dsimp <;> omega
lemma actualTail_full_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+
      CallOperator (actualTrigonometric 1 z hz hzB)-AallOperator (actualTrigonometric 0 z hz hzB)+
      tailTarget z hz hzB+(3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+
      CallOperator (actualTrigonometric 0 z hz hzB)-AallOperator (actualTrigonometric 1 z hz hzB)-
      (3/500:ℝ) • tailFixedColumn 22 := by
  rcases actualTail_equations hz hzB with ⟨h0,h1⟩
  simp only [actualTrigonometric,map_add,CallOperator_extend,AallOperator_extend]
  constructor
  · rw [h0]; abel
  · rw [h1]; abel
end AtomicTriangular.Construction
end

end OAI
