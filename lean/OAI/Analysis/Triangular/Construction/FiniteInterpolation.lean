import OAI.Analysis.Triangular.Construction.FiniteSystem
import OAI.Analysis.Triangular.Construction.FiniteAssembly
import OAI.Analysis.Triangular.Construction.FiniteTargetBridge
import OAI.Analysis.Triangular.Construction.TailInterpolation

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma Roperator_apply (u : FiniteCoefficients) (i : Fin 20) :
    Roperator u i=∑ j : Fin 20,R i j*u j := by
  unfold Roperator
  erw [operator_apply,tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
lemma extendFiniteError_fixed (u : FiniteCoefficients) (i : Fin 2) :
    extendFiniteError u ⟨i.val,by omega⟩=0 := by
  change (if hi : i.val<2 then _ else _)=_
  simp only [i.isLt,↓reduceDIte]
lemma extendFiniteError_shift (u : FiniteCoefficients) (i : Fin 20) :
    extendFiniteError u ⟨i.val+2,by omega⟩=u i := by
  change (if hi : i.val+2<2 then 0 else u ⟨i.val+2-2,by omega⟩)=_
  simp only [show ¬(i.val+2<2) by omega,↓reduceDIte]
  congr 1
lemma extendFiniteError_transformed (u : FiniteCoefficients) (i : Fin 20) :
    (∑ c : Fin 22,extendFiniteError u c*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨c.val,by omega⟩))=Roperator u i := by
  have hh := finiteRow_sum 0 (extendFiniteError u) i
  have h0 : extendFiniteError u 0=0 := extendFiniteError_fixed u 0
  have h1 : extendFiniteError u 1=0 := extendFiniteError_fixed u 1
  erw [h0] at hh
  simp only [extendFiniteError_shift,zero_mul,zero_add,mul_zero,add_zero] at hh
  rw [hh,Roperator_apply]
lemma actualTrigonometric_shift (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    actualTrigonometric side z hz hzB ⟨i.val+2,by omega⟩=
      (finiteSolution side *ᵥ actualParameter z) i+actualFiniteError side z hz hzB i := by
  change finiteApprox side (actualParameter z) _+extendFiniteError (actualFiniteError side z hz hzB) _=_
  rw [finiteApprox_shift,extendFiniteError_shift]
lemma actualInput_row_transformed (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i)
      (inputJJet (actualInput side z hz hzB) 1 0 (rowNode i).val)
      (inputJJet (actualInput side z hz hzB) 1 1 (rowNode i).val)).re=
      Boperator (actualTail side z hz hzB) i+Roperator (actualFiniteError side z hz hzB) i+
      (R *ᵥ (finiteSolution side *ᵥ actualParameter z)+R0 *ᵥ (gamma side *ᵥ actualParameter z)) i := by
  rw [actualInput,inputJJet_row_transformed]
  simp only [actualTrigonometric,lp.coeFn_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  rw [extendFiniteError_transformed]
  have hh := finiteApprox_transformed side (actualParameter z) i
  have hc : (gamma side *ᵥ actualParameter z) 2=if side.val=0 then -(3/500) else 3/500 := by
    rw [gamma_actual]
    rfl
  rw [hc] at hh
  simp only [Pi.add_apply] at hh
  linarith
lemma actual_finite_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 (rowNode i).val)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 (rowNode i).val)).re=
      -gaussianTarget H z (rowNode i).val (rowDerivative i) ∧
    (negativeJet H (rowNode i).val (rowDerivative i)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 (rowNode i).val)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 (rowNode i).val)).re=0 := by
  have h0 := congrArg (fun u : FiniteCoefficients => u i) (actualFiniteError_equations hz hzB).1
  have h1 := congrArg (fun u : FiniteCoefficients => u i) (actualFiniteError_equations hz hzB).2
  simp only [lp.coeFn_add,Pi.add_apply] at h0 h1
  have hf0 := congrArg (fun A : Matrix (Fin 20) (Fin 8) ℝ => (A *ᵥ actualParameter z) i) finiteSolution_equations.1
  have hf1 := congrArg (fun A : Matrix (Fin 20) (Fin 8) ℝ => (A *ᵥ actualParameter z) i) finiteSolution_equations.2
  simp only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,Pi.add_apply] at hf0 hf1
  have hy := Yf_residual z i
  simp only [pairJJet_negative,add_re,actualInput_row_transformed,Pi.add_apply]
  have hd (side : Fin 2) :
      (negativeJet H (rowNode i).val (rowDerivative i)
        (inputJJet (actualInput side z hz hzB) 0 0 (rowNode i).val)
        (inputJJet (actualInput side z hz hzB) 0 1 (rowNode i).val)).re=
        -((finiteSolution side *ᵥ actualParameter z) i+actualFiniteError side z hz hzB i) := by
    rw [actualInput,inputJJet_row_direct_negative,actualTrigonometric_shift]
  simp only [hd]
  change _= -gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ ∧ _=0
  constructor <;> linarith
end AtomicTriangular.Construction
end

end OAI
