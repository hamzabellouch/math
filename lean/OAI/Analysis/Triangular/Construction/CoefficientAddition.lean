import OAI.Analysis.Triangular.Construction.ActualInterpolation
import OAI.Analysis.Triangular.Construction.FinitePairBridge

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma inputJJet_split (C : ℝ) (a da : TrigonometricCoefficients) (w : TailCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C (a+da) w) br k s=
      inputJJet (coefficientInput C a 0) br k s+inputJJet (coefficientInput 0 da w) br k s := by
  have hzero (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : (0:ℂ) • T=0 := by
    ext f
    exact zero_mul _
  simp only [hzero,inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    lp.coeFn_add,lp.coeFn_zero,Pi.zero_apply,add_zero,tsum_zero,Pi.add_apply,ofReal_add,ofReal_zero,zero_add,_root_.add_apply,
    _root_.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
  ring
lemma gamma_actual_constant (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z) 2=if side.val=0 then -(3/500:ℝ) else 3/500 := by
  rw [gamma_actual]
  rfl
lemma actualJ_split (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualJ side z hz hzB = finiteJ side (actualParameter z)+
      pairJ (coefficientInput 0 (extendFiniteError (actualFiniteError side z hz hzB)) (actualTail side z hz hzB))
        (coefficientInput 0 (extendFiniteError (actualFiniteError (otherSide side) z hz hzB)) (actualTail (otherSide side) z hz hzB)) := by
  funext s
  simp only [Pi.add_apply,actualJ,actualInput,actualTrigonometric,finiteJ,finiteJJet_pair,pairJ,pairJJet,inputJJet_split,gamma_actual_constant]
  simp only [add_re]
  ring
end AtomicTriangular.Construction
end

end OAI
