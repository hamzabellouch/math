import OAI.Analysis.Triangular.Construction.ActualCorrection

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma tail_pairs_summable (w : TailCoefficients) :
    Summable (fun n => |w (n,0)|+|w (n,1)|) := by
  have hh := (l1_summable w).prod
  simpa [tsum_fintype,Fin.sum_univ_succ] using hh
lemma tail_pairs_norm (w : TailCoefficients) :
    (∑' n, (|w (n,0)| + |w (n,1)|))=‖w‖ := by
  rw [l1_norm]
  symm
  calc
    (∑' p, |w p|) = ∑' n : TailNode, ∑' d : Fin 2, |w (n,d)| := (l1_summable w).tsum_prod
    _ = _ := by simp only [tsum_fintype,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
                rfl

def coefficientInput (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) : InputCoefficients where
  C := C
  finiteC j := a ⟨2*j.val,by omega⟩
  finiteD j := a ⟨2*j.val+1,by omega⟩
  tailC n := w (n,0)
  tailD n := w (n,1)
  summable := tail_pairs_summable w

def extendFiniteError (u : FiniteCoefficients) : TrigonometricCoefficients :=
  column (fun i (_ : Unit) => if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)
    (fun _ => (hasSum_fintype _).summable) ()
lemma extendFiniteError_norm (u : FiniteCoefficients) : ‖extendFiniteError u‖=‖u‖ := by
  rw [l1_norm,l1_norm,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, |if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩|)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,abs_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 2

def actualTrigonometric (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TrigonometricCoefficients :=
  finiteApprox side (actualParameter z)+extendFiniteError (actualFiniteError side z hz hzB)
def actualInput (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : InputCoefficients :=
  coefficientInput (if side.val=0 then -(3/500) else 3/500)
    (actualTrigonometric side z hz hzB) (actualTail side z hz hzB)
lemma actualTrigonometric_norm (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualTrigonometric side z hz hzB‖ < (300001/100000:ℝ) := by
  have h1 := finiteApprox_norm side (actualParameter z) (actualParameter_mem hz hzB)
  have h2 := actualFiniteError_norm side hz hzB
  have hh := norm_add_le (finiteApprox side (actualParameter z)) (extendFiniteError (actualFiniteError side z hz hzB))
  rw [extendFiniteError_norm] at hh
  change ‖finiteApprox side (actualParameter z)+_‖ < _
  linarith

lemma correctionFinite_plus (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionFinite 0 r s = Roperator (correctionFinite 0 r s)+Boperator (correctionTail 0 r s)+r := by
  have hh := congrArg (fun T : FiniteCoefficients →L[ℝ] FiniteCoefficients => T (r+Boperator (correctionTail 0 r s))) Lplus_left_inverse
  change correctionFinite 0 r s-Roperator (correctionFinite 0 r s)=r+Boperator (correctionTail 0 r s) at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (by abel)
lemma correctionFinite_minus (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionFinite 1 r s = -Roperator (correctionFinite 1 r s)-Boperator (correctionTail 1 r s)+r := by
  have hh := congrArg (fun T : FiniteCoefficients →L[ℝ] FiniteCoefficients => T (r-Boperator (correctionTail 1 r s))) Lminus_left_inverse
  change correctionFinite 1 r s+Roperator (correctionFinite 1 r s)=r-Boperator (correctionTail 1 r s) at hh
  exact eq_sub_of_add_eq hh |>.trans (by abel)
lemma actualFiniteError_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualFiniteError 0 z hz hzB = Roperator (actualFiniteError 1 z hz hzB)+Boperator (actualTail 1 z hz hzB)+finiteResidual z ∧
    actualFiniteError 1 z hz hzB = Roperator (actualFiniteError 0 z hz hzB)+Boperator (actualTail 0 z hz hzB) := by
  have hp := correctionFinite_plus (finiteResidual z) (approximationTailResidual 0 z hz hzB)
  have hm := correctionFinite_minus (finiteResidual z) (approximationTailResidual 1 z hz hzB)
  change actualFiniteSplit 0 z hz hzB=Roperator (actualFiniteSplit 0 z hz hzB)+Boperator (actualTailSplit 0 z hz hzB)+finiteResidual z at hp
  change actualFiniteSplit 1 z hz hzB= -Roperator (actualFiniteSplit 1 z hz hzB)-Boperator (actualTailSplit 1 z hz hzB)+finiteResidual z at hm
  constructor <;> ext i
  all_goals
    have hp' := congrArg (fun u : FiniteCoefficients => u i) hp
    have hm' := congrArg (fun u : FiniteCoefficients => u i) hm
    simp only [actualFiniteError,actualTail,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
      map_smul,map_add,map_neg,lp.coeFn_add,lp.coeFn_sub,lp.coeFn_neg,lp.coeFn_smul,
      Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hp' hm' ⊢
    linarith
end AtomicTriangular.Construction
end

end OAI
