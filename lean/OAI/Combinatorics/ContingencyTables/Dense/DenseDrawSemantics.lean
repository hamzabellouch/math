import OAI.Combinatorics.ContingencyTables.Dense.DenseDrawProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialSemantics
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanDraw

namespace OAI

/-! # The bounded binary draw is exactly the analyzed Boolean sampler -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

lemma trialWidth_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) :
    trialWidth ((((marginCode R,marginCode P),gridNatCode a),d),h)=
      denseTrialBits R P d finProdFinEquiv h := by
  unfold trialWidth
  rw [flatToGridData_code,offsetLengths_code,List.sum_ofFn]
  rfl

lemma denseTrialBits_pos {m n d : ℕ} (hd : 0 < d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (h : ℕ) :
    0 < denseTrialBits R P d finProdFinEquiv h := by
  have hw := denseStepBits_pos hd
  have ht : 0 < (d^50*(h+1)^2)*denseStepBits d := by positivity
  unfold denseTrialBits
  omega

def drawInput {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : List Bool) : DenseDrawData :=
  ((((((marginCode R,marginCode P),gridNatCode a),d),h),tableOutput fallback),bits)

/-- This identifies every output, including the all-rejections fallback,
with the actual finite Boolean sampler whose total-variation bound is proved. -/
theorem denseDrawCode_eq {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : Fin (denseDrawBits R P d finProdFinEquiv h) → Bool) :
    denseDrawCode (drawInput R P h a fallback (List.ofFn bits))=
      tableOutput (denseBooleanDraw R P d hd hR hP finProdFinEquiv htotal h a fallback bits) := by
  have hd0 : 0 < d := by omega
  unfold denseDrawCode drawChunks drawInput
  dsimp only [Prod.fst,Prod.snd]
  rw [trialWidth_code]
  have hc := wordChunks_ofFn (n := d^4*(h+1)) (denseTrialBits_pos hd0 R P h) bits
  let params : DenseDrawParameters := ((((marginCode R,marginCode P),gridNatCode a),d),h)
  have he := congrArg (fun ws => FirstSuccessProgram.retry denseTrialCode
    ((params,tableOutput fallback),ws)) hc
  refine he.trans ?_
  rw [FirstSuccessProgram.retry_ofFn]
  have ht : (fun word => denseTrialCode
      (((((marginCode R,marginCode P),gridNatCode a),d),h),List.ofFn word))=
      fun word => (trialSuccess R P d finProdFinEquiv htotal
        (denseBooleanTrial R P d hd hR hP finProdFinEquiv h a word)).map tableOutput := by
    funext word
    exact denseTrialCode_eq R P hd hR hP htotal h a word
  rw [ht,FirstSuccessProgram.wordRetry_map]
  rfl

end
end ContingencyTables.DensePrograms

end OAI
