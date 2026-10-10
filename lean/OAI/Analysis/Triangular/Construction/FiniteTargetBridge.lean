import OAI.Analysis.Triangular.Construction.ActualCorrection

namespace OAI

noncomputable section
open scoped BigOperators lp
open Matrix
namespace AtomicTriangular.Construction
lemma gaussianTarget_factor (z : ℝ) (n : Fin 10) (d : Fin 2) :
    gaussianTarget H z (finiteNode n) d=targetCoefficient n * Real.exp ((1-finiteNode n)/z)*
      (if d.val=0 then z else -1+(Real.pi*eta-D (finiteNode n))*z) := by
  have he : H-h=eta := by norm_num [H,h,eta]
  simp only [gaussianTarget,targetCoefficient,he,Real.exp_add]
  ring
lemma Yf_actual (z : ℝ) (i : Fin 20) :
    (Yf *ᵥ actualParameter z) i=
      if i.val<8 then gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ else 0 := by
  rw [gaussianTarget_factor]
  fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Yf,actualParameter,Fin.sum_univ_succ,
    finiteNode,residue] <;> ring
lemma Yf_residual (z : ℝ) (i : Fin 20) :
    (Yf *ᵥ actualParameter z) i+finiteResidual z i=
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ := by
  rw [Yf_actual]
  change (if i.val<8 then _ else 0)+(if i.val<8 then 0 else _)=_
  split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
