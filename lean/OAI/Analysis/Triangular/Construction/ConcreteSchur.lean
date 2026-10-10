import OAI.Analysis.Triangular.Construction.RepetitionOperators
import OAI.Analysis.Triangular.Construction.Schur

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def splitL (e : Fin 2) : FiniteCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Lplus else Lminus
def splitB (e : Fin 2) : TailCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Boperator else -Boperator
def splitK (e : Fin 2) : FiniteCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Coperator-Aoperator else -Coperator-Aoperator
def splitD (e : Fin 2) : TailCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Doperator else -Doperator
def splitN (e : Fin 2) : ℝ := if e.val=0 then 17 else 5
def splitQ (e : Fin 2) : ℝ := delta+340*beta*splitN e
lemma splitL_norm (e : Fin 2) : ‖splitL e‖ ≤ splitN e := by
  fin_cases e
  · exact Lplus_norm
  · exact Lminus_norm
lemma splitB_norm (e : Fin 2) : ‖splitB e‖ ≤ 340 := by
  have hh := Boperator_norm
  fin_cases e <;> simp only [splitB,↓reduceIte,Nat.one_ne_zero,norm_neg] <;> linarith
lemma splitK_norm (e : Fin 2) : ‖splitK e‖ ≤ beta := by
  have ha := AC_bound
  fin_cases e
  · exact (norm_sub_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by simpa only [norm_neg] using (show ‖Coperator‖+‖Aoperator‖≤beta by linarith))
lemma splitD_norm (e : Fin 2) : ‖splitD e‖ ≤ delta := by
  have hh := Doperator_norm
  fin_cases e <;> simp only [splitD,↓reduceIte,Nat.one_ne_zero,norm_neg] <;>
    norm_num [delta] at * <;> linarith
lemma splitN_nonneg (e : Fin 2) : 0 ≤ splitN e := by fin_cases e <;> norm_num [splitN]
lemma splitQ_nonneg (e : Fin 2) : 0 ≤ splitQ e := by fin_cases e <;> norm_num [splitQ,splitN,beta,delta]
lemma splitQ_lt (e : Fin 2) : splitQ e<1 := by fin_cases e <;> norm_num [splitQ,splitN,beta,delta]
lemma splitOperator_norm (e : Fin 2) :
    ‖tailOperator (splitL e) (splitB e) (splitK e) (splitD e)‖ ≤ splitQ e := by
  have hb : 0≤beta := by norm_num [beta]
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖splitD e‖+‖(splitK e).comp ((splitL e).comp (splitB e))‖ := norm_add_le _ _
    _ ≤ delta+‖splitK e‖*(‖splitL e‖*‖splitB e‖) :=
      add_le_add (splitD_norm e) ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)))
    _ ≤ delta+beta*(splitN e*340) := by
      gcongr
      · exact splitK_norm e
      · exact splitL_norm e
      · exact splitB_norm e
    _ = splitQ e := by unfold splitQ; ring

def correctionTail (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) : TailCoefficients :=
  tailSolution (splitL e) (splitB e) (splitK e) (splitD e) r s
def correctionFinite (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) : FiniteCoefficients :=
  AtomicTriangular.Schur.finiteSolution (splitL e) (splitB e) (splitK e) (splitD e) r s
lemma correctionTail_equation (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionTail e r s = splitD e (correctionTail e r s) +
      splitK e (correctionFinite e r s)+s :=
  solution_equations _ _ _ _ _ _ ((splitOperator_norm e).trans_lt (splitQ_lt e))
lemma correctionTail_norm (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    ‖correctionTail e r s‖ ≤ (‖s‖+beta*splitN e*‖r‖)/(1-splitQ e) := by
  have hn := neumann_norm (tailOperator (splitL e) (splitB e) (splitK e) (splitD e))
    (splitQ_nonneg e) (splitQ_lt e) (splitOperator_norm e)
  have hq : 0≤1/(1-splitQ e) := by exact div_nonneg (by norm_num) (sub_pos.mpr (splitQ_lt e)).le
  have hbeta : 0≤beta := by norm_num [beta]
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖neumann (tailOperator (splitL e) (splitB e) (splitK e) (splitD e))‖*
        ‖s+splitK e (splitL e r)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1/(1-splitQ e))*(‖s‖+‖splitK e‖*(‖splitL e‖*‖r‖)) := by
      apply mul_le_mul hn _ (norm_nonneg _) hq
      exact (norm_add_le _ _).trans (add_le_add_right ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) _)
    _ ≤ (1/(1-splitQ e))*(‖s‖+beta*(splitN e*‖r‖)) := by
      gcongr
      · exact splitK_norm e
      · exact splitL_norm e
    _ = _ := by ring
lemma correctionFinite_norm (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    ‖correctionFinite e r s‖ ≤ splitN e*(‖r‖+340*‖correctionTail e r s‖) := by
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖splitL e‖*‖r+splitB e (correctionTail e r s)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ splitN e*(‖r‖+‖splitB e‖*‖correctionTail e r s‖) :=
      mul_le_mul (splitL_norm e) ((norm_add_le _ _).trans
        (add_le_add_right (ContinuousLinearMap.le_opNorm _ _) _)) (norm_nonneg _) (splitN_nonneg e)
    _ ≤ _ := by gcongr; exact splitB_norm e

def finiteResidualBound : ℝ := 82/10^9
def tailResidualBound (e : Fin 2) : ℝ := 1/10^26+6*beta+(if e.val=0 then 0 else (12/1000)*(13/10^8))
def tailErrorBound (e : Fin 2) : ℝ := if e.val=0 then 1801/10^12 else 3361/10^12
def finiteErrorBound (e : Fin 2) : ℝ := if e.val=0 then 11804/10^9 else 6124/10^9
lemma correctionTail_small (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
    (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
    ‖correctionTail e r s‖ ≤ tailErrorBound e := by
  have hh := correctionTail_norm e r s
  have hb : (‖s‖+beta*splitN e*‖r‖)/(1-splitQ e) ≤
      (tailResidualBound e+beta*splitN e*finiteResidualBound)/(1-splitQ e) := by
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr (splitQ_lt e)).le
    apply add_le_add hs
    exact mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num [beta]) (splitN_nonneg e))
  refine (hh.trans hb).trans ?_
  fin_cases e <;> norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]
lemma correctionFinite_small (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
    (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
    ‖correctionFinite e r s‖ ≤ finiteErrorBound e := by
  have hN := splitN_nonneg e
  have hh := correctionFinite_norm e r s
  have hb := correctionTail_small e r s hr hs
  calc
    _ ≤ splitN e*(‖r‖+340*‖correctionTail e r s‖) := hh
    _ ≤ splitN e*(finiteResidualBound+340*tailErrorBound e) := by gcongr
    _ ≤ _ := by fin_cases e <;> norm_num [splitN,finiteResidualBound,tailErrorBound,finiteErrorBound]
end AtomicTriangular.Construction
end

end OAI
