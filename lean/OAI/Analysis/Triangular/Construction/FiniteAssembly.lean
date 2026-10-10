import OAI.Analysis.Triangular.Construction.FiniteProjection

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma finiteRow_sum (C : ℝ) (a : Fin 22 → ℝ) (i : Fin 20) :
    C*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,a c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩))=
    (∑ j : Fin 20,R i j*a ⟨j.val+2,by omega⟩)+
      R0 i 0*a 0+R0 i 1*a 1+R0 i 2*C := by
  have hR (j : Fin 20) : R i j=jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨j.val+2,by omega⟩) := by
    simp only [R,fullJetMatrix,show j.val+2≠22 by omega,↓reduceIte,rowNode,rowDerivative]
  simp_rw [hR]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  have hh : (∑ j : Fin 20,a j.succ.succ*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨j.succ.succ.val,by omega⟩))=
      ∑ j : Fin 20,jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨j.val+2,by omega⟩)*a ⟨j.val+2,by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    have he : j.succ.succ=(⟨j.val+2,by omega⟩:Fin 22) := Fin.ext (by simp)
    simp only [he]
    exact mul_comm _ _
  rw [hh]
  simp only [R0,fullJetMatrix,Fin.val_zero,Fin.val_one,Fin.val_two,show 0<2 by omega,
    show 1<2 by omega,lt_self_iff_false,↓reduceIte,show (0:ℕ)≠22 by omega,show (1:ℕ)≠22 by omega]
  change _= _
  dsimp [rowNode,rowDerivative]
  ring
lemma finiteApprox_shift (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 20) :
    finiteApprox side e ⟨i.val+2,by omega⟩=(finiteSolution side *ᵥ e) i := by
  change (∑ j : Fin 8,Acoefficient side ⟨i.val+2,by omega⟩ j*e j)=_
  simp only [Acoefficient,show ¬(i.val+2<2) by omega,show i.val+2≠22 by omega,↓reduceDIte]
  rfl
lemma finiteApprox_fixed (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 2) :
    finiteApprox side e ⟨i.val,by omega⟩=(gamma side *ᵥ e) ⟨i.val,by omega⟩ := by
  change (∑ j : Fin 8,Acoefficient side ⟨i.val,by omega⟩ j*e j)=_
  simp only [Acoefficient,show i.val<2 from i.isLt,↓reduceDIte]
  rfl
lemma finiteApprox_transformed (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 20) :
    (gamma side *ᵥ e) 2*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,finiteApprox side e c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩))=
      (R *ᵥ (finiteSolution side *ᵥ e)+R0 *ᵥ (gamma side *ᵥ e)) i := by
  rw [finiteRow_sum]
  simp only [finiteApprox_shift]
  have h0 : finiteApprox side e 0=(gamma side *ᵥ e) 0 := finiteApprox_fixed side e 0
  have h1 : finiteApprox side e 1=(gamma side *ᵥ e) 1 := finiteApprox_fixed side e 1
  erw [h0,h1]
  change (∑ j : Fin 20,R i j*(finiteSolution side *ᵥ e) j)+_+_+_=
    (∑ j : Fin 20,R i j*(finiteSolution side *ᵥ e) j)+(∑ j : Fin 3,R0 i j*(gamma side *ᵥ e) j)
  rw [Fin.sum_univ_three]
  abel
lemma gamma_actual (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z)= ![11/25,0,if side.val=0 then -(3/500) else 3/500] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,gamma,Fin.sum_univ_succ,actualParameter]
lemma inputJJet_row_transformed (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i) (inputJJet (coefficientInput C a w) 1 0 (rowNode i).val)
      (inputJJet (coefficientInput C a w) 1 1 (rowNode i).val)).re=
    Boperator w i + C*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,a c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩)) := by
  rw [inputJJet_negative_coefficient]
  have hb : Boperator w i=∑' p : TailNode × Fin 2,w p*tailJet h H (rowNode i).val p.1.val.val p.2 (rowDerivative i) := by
    unfold Boperator
    erw [operator_apply]
    rfl
  rw [hb]
  ring
end AtomicTriangular.Construction
end

end OAI
