import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.LoopInput2

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList.Set

def pack (xs j v : List Bool) : List Bool := pairBits (xs,pairBits (j,v))
def target (x : List Bool) : List Bool := extractPrefix (discardPrefix (extractPrefix x))
def replacement (x : List Bool) : List Bool := discardPrefix (discardPrefix (extractPrefix x))
def oldInput (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix (extractPrefix x))
def oldValue (x : List Bool) : List Bool := Lookup.run (oldInput x)
noncomputable def target_computes : PolyComputes target :=
  (extractPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def replacement_computes : PolyComputes replacement :=
  (extractPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def oldInput_computes : PolyComputes oldInput :=
  discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)
noncomputable def oldValue_computes : PolyComputes oldValue := oldInput_computes.comp Lookup.run_computes

def op (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (target x) then
    if value (target x)≤value (discardPrefix x) then replacement x else oldValue x
  else oldValue x
noncomputable def op_computes : PolyComputes op := by
  have hl := NatOps.le discardPrefix_computes target_computes
  have hr := NatOps.le target_computes discardPrefix_computes
  have hh := hl.cond (hr.cond replacement_computes oldValue_computes) oldValue_computes
  unfold op
  simpa only [decide_eq_true_eq] using hh
lemma op_ofFn {n : ℕ} (w : Fin n → List Bool) (i j : Fin n) (v : List Bool) :
    op (pairBits (pack (encode (List.ofFn w)) j.val.bits v,i.val.bits))=
      (if i=j then v else w i) := by
  simp only [op,pack,target,replacement,oldValue,oldInput,extractPrefix_pairBits,
    discardPrefix_pairBits,value_bits,lookup_ofFn]
  split_ifs <;> try rfl
  all_goals omega

noncomputable def input (x : List Bool) : List Bool := pairBits (x,Indices.run (extractPrefix x))
noncomputable def input_computes : PolyComputes input :=
  id_computes.pair (extractPrefix_computes.comp Indices.run_computes)
noncomputable def run (x : List Bool) : List Bool := mapWith op (input x)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=input) (g:=mapWith op) input_computes (mapWith_computes op_computes))
lemma run_ofFn {n : ℕ} (w : Fin n → List Bool) (j : Fin n) (v : List Bool) :
    run (pack (encode (List.ofFn w)) j.val.bits v)=
      encode (List.ofFn (fun i=>if i=j then v else w i)) := by
  simp only [run,input,pack,extractPrefix_pairBits,indices_ofFn,mapWith_ofFn]
  have hh (i : Fin n) := op_ofFn w i j v
  simp only [pack] at hh
  simp only [hh]
end WordList.Set
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def updateInput (x : List Bool) : List Bool :=
  Set.pack (transposeWords (extractPrefix x)) (extractPrefix (discardPrefix x))
    (discardPrefix (discardPrefix x))
noncomputable def updateInput_computes : PolyComputes updateInput := by
  unfold updateInput Set.pack
  simpa only [Function.comp_def] using
    ((PolyComputes.comp (f:=extractPrefix) (g:=transposeWords)
      extractPrefix_computes transposeWords_computes).pair
    ((discardPrefix_computes.comp extractPrefix_computes).pair
      (discardPrefix_computes.comp discardPrefix_computes)))
noncomputable def updateColWords (x : List Bool) : List Bool :=
  transposeWords (Set.run (updateInput x))
noncomputable def updateColWords_computes : PolyComputes updateColWords := by
  unfold updateColWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=Set.run ∘ updateInput) (g:=transposeWords)
      (PolyComputes.comp (f:=updateInput) (g:=Set.run) updateInput_computes Set.run_computes)
      transposeWords_computes)
lemma updateColWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) (j : Fin n) :
    updateColWords (Set.pack (encode A) j.val.bits (rowEncode b))=encode (A.updateCol j b) := by
  have he : WordList.encode (List.ofFn (fun i=>if i=j then rowEncode b else rowEncode (A.transpose i)))=
      encode (A.updateCol j b).transpose := by
    rw [encode]
    congr 1
    apply congrArg List.ofFn
    funext i
    by_cases hi : i=j
    · subst i
      rw [ite_eq_left rfl]
      apply congrArg rowEncode
      funext k
      simp only [Matrix.transpose_apply,Matrix.updateCol_self]
    · rw [ite_eq_right hi]
      apply congrArg rowEncode
      funext k
      simp only [Matrix.transpose_apply,Matrix.updateCol_ne hi]
  unfold updateColWords updateInput
  simp only [Set.pack,extractPrefix_pairBits,discardPrefix_pairBits,transposeWords_encode]
  rw [encode,←Set.pack,Set.run_ofFn,he,transposeWords_encode,Matrix.transpose_transpose]

def cramerOpInput (x : List Bool) : List Bool :=
  Set.pack (extractPrefix (extractPrefix x)) (discardPrefix x) (discardPrefix (extractPrefix x))
noncomputable def cramerOpInput_computes : PolyComputes cramerOpInput :=
  (extractPrefix_computes.comp extractPrefix_computes).pair
    (discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes))
noncomputable def cramerOp (x : List Bool) : List Bool :=
  determinantWords (updateColWords (cramerOpInput x))
noncomputable def cramerOp_computes : PolyComputes cramerOp := by
  unfold cramerOp
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=updateColWords ∘ cramerOpInput) (g:=determinantWords)
      (PolyComputes.comp (f:=cramerOpInput) (g:=updateColWords)
        cramerOpInput_computes updateColWords_computes) determinantWords_computes)
lemma cramerOp_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) (j : Fin n) :
    cramerOp (pairBits (pairBits (encode A,rowEncode b),j.val.bits))=
      BinaryRational.encode ((A.updateCol j b).det) := by
  simp only [cramerOp,cramerOpInput,extractPrefix_pairBits,discardPrefix_pairBits,
    updateColWords_encode,determinantWords_encode]
noncomputable def cramerInput (x : List Bool) : List Bool := pairBits (x,Indices.run (extractPrefix x))
noncomputable def cramerInput_computes : PolyComputes cramerInput :=
  id_computes.pair (extractPrefix_computes.comp Indices.run_computes)
noncomputable def cramerWords (x : List Bool) : List Bool := mapWith cramerOp (cramerInput x)
noncomputable def cramerWords_computes : PolyComputes cramerWords := by
  unfold cramerWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=cramerInput) (g:=mapWith cramerOp)
      cramerInput_computes (mapWith_computes cramerOp_computes))
lemma cramerWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    cramerWords (pairBits (encode A,rowEncode b))=rowEncode (A.cramer b) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  simp only [cramerWords,cramerInput,extractPrefix_pairBits,hi,mapWith_ofFn,cramerOp_encode]
  simp only [rowEncode_eq,Matrix.cramer_apply]

noncomputable def firstDet : List Bool → List Bool := determinantWords ∘ extractPrefix
noncomputable def firstDet_computes : PolyComputes firstDet :=
  PolyComputes.comp (f:=extractPrefix) (g:=determinantWords) extractPrefix_computes determinantWords_computes
noncomputable def inverseDet : List Bool → List Bool := BinaryRational.invWords ∘ firstDet
noncomputable def inverseDet_computes : PolyComputes inverseDet :=
  PolyComputes.comp (f:=firstDet) (g:=BinaryRational.invWords) firstDet_computes BinaryRational.invWords_computes
noncomputable def solveInput (x : List Bool) : List Bool := pairBits (inverseDet x,cramerWords x)
noncomputable def solveInput_computes : PolyComputes solveInput := inverseDet_computes.pair cramerWords_computes
noncomputable def solveWords (x : List Bool) : List Bool := mapWith BinaryRational.mulWords (solveInput x)
noncomputable def solveWords_computes : PolyComputes solveWords := by
  unfold solveWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=solveInput) (g:=mapWith BinaryRational.mulWords)
      solveInput_computes (mapWith_computes BinaryRational.mulWords_computes))
lemma solveWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solveWords (pairBits (encode A,rowEncode b))=rowEncode (A.det⁻¹ • A.cramer b) := by
  simp only [solveWords,solveInput,inverseDet,firstDet,Function.comp_apply,extractPrefix_pairBits,determinantWords_encode,
    BinaryRational.invWords_encode,cramerWords_encode]
  simp only [rowEncode_eq,mapWith_ofFn,
    BinaryRational.mulWords_pair,Pi.smul_apply,smul_eq_mul]

lemma solveWords_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : A.det≠0) : A *ᵥ (A.det⁻¹ • A.cramer b)=b := by
  rw [Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hA,one_smul]

lemma solveWords_bird {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solveWords (pairBits (encode A,rowEncode b))=rowEncode (MetricKMedianRecovery.BirdRational.solve A b) := by
  rw [solveWords_encode]
  congr 1
  symm
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    let D : ℚ := MetricKMedianRecovery.BirdRational.commonDen (MetricKMedianRecovery.BirdRational.data A b)
    have hD : D≠0 := by
      dsimp [D]
      exact_mod_cast (MetricKMedianRecovery.BirdRational.commonDen_pos (MetricKMedianRecovery.BirdRational.data A b)).ne'
    have hZ : (MetricKMedianRecovery.BirdRational.integerMatrix A b).map (Int.cast : ℤ → ℚ)=D • A :=
      MetricKMedianRecovery.BirdRational.integerMatrix_cast A b
    rw [MetricKMedianRecovery.BirdRational.solve_as_cramer,hZ,MetricKMedianRecovery.BirdRational.integerVector_cast,
      Matrix.det_smul,Matrix.cramer_smul,LinearMap.smul_apply,map_smul,
      smul_smul,smul_smul]
    simp only [Fintype.card_fin,Nat.add_sub_cancel]
    change ((D^(n+1)*A.det)⁻¹*D^n*D) • (A.cramer b)=_
    rw [mul_assoc,←pow_succ,mul_inv_rev,mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hD),mul_one]

noncomputable def solve {n : ℕ} : Turing.TM2ComputableInPolyTime
    (fun p : Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)=>pairBits (encode p.1,rowEncode p.2))
    rowEncode (fun p=>MetricKMedianRecovery.BirdRational.solve p.1 p.2) :=
  solveWords_computes.reencode _ _ (fun p=>solveWords_bird p.1 p.2)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
