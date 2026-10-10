import OAI.Analysis.Triangular.Construction.ActualTail
import OAI.Analysis.Triangular.Construction.TailCoordinates

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma inputJJet_tail_transformed (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2 (inputJJet (coefficientInput C a w) 1 0 p.1.val.val)
      (inputJJet (coefficientInput C a w) 1 1 p.1.val.val)).re=
      Doperator w p+CallOperator a p+C*tailFixedColumn 22 p := by
  rw [inputJJet_negative_coefficient]
  have hd : Doperator w p=∑' q : TailNode × Fin 2,w q*tailJet h h p.1.val.val q.1.val.val q.2 p.2 := by
    unfold Doperator
    erw [operator_apply]
    rfl
  have hc : CallOperator a p=∑ c : Fin 22,a c*jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩) := by
    unfold CallOperator
    erw [operator_apply,tsum_fintype]
    rfl
  rw [hd,hc,tailFixedColumn_apply]
  simp only [show (22:Fin 23).val=22 from rfl,↓reduceIte]
  ring
lemma pairJJet_negative (a₁ a₂ : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (pairJJet a₁ a₂ 0 n) (pairJJet a₁ a₂ 1 n)=
      negativeJet v n d (inputJJet a₁ 0 0 n) (inputJJet a₁ 0 1 n)+
      negativeJet v n d (inputJJet a₂ 1 0 n) (inputJJet a₂ 1 1 n) := by
  exact negativeJet_add _ _ _ _ _ _ _
lemma actual_tail_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 p.1.val.val)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 p.1.val.val)).re=
        -gaussianTarget h z p.1.val.val p.2 ∧
    (negativeJet h p.1.val.val p.2
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 p.1.val.val)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 p.1.val.val)).re=0 := by
  have h0 := congrArg (fun w : TailCoefficients => w p) (actualTail_full_equations hz hzB).1
  have h1 := congrArg (fun w : TailCoefficients => w p) (actualTail_full_equations hz hzB).2
  simp only [lp.coeFn_add,lp.coeFn_sub,lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,
    Pi.smul_apply,smul_eq_mul] at h0 h1
  change _=_+_ -_ +gaussianTarget h z p.1.val.val p.2+(3/500)*tailFixedColumn 22 p at h0
  simp only [pairJJet_negative,add_re,actualInput,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
    inputJJet_tail_direct_negative,inputJJet_tail_transformed]
  constructor <;> linarith
end AtomicTriangular.Construction
end

end OAI
