import OAI.Combinatorics.ParityLifts.BoundedSimulation

namespace OAI

namespace ParityWL.Complexity

def trialInput (j k : ℕ) (bs : List Bool) : List Bool :=
  List.replicate j true++false::(List.replicate k true++false::bs)

def readUnary (bs : List Bool) : ℕ × List Bool := (truePrefix bs,bs.drop (truePrefix bs+1))

def PolyProgram.readUnary : PolyProgram (List Bool) (ℕ × List Bool) readUnary := by
  let n := PolyProgram.truePrefix
  let rem := (((n.comp PolyProgram.natSucc).pair (PolyProgram.id (List Bool))).comp
    (PolyProgram.splitAt Bool)).comp (PolyProgram.snd (List Bool) (List Bool))
  exact n.pair rem

lemma readUnary_encode (n : ℕ) (bs : List Bool) :
    readUnary (List.replicate n true++false::bs)=(n,bs) := by
  have h : truePrefix (List.replicate n true++false::bs)=n := by
    induction n with
    | zero => simp [truePrefix]
    | succ n ih => simp [List.replicate_succ,truePrefix,ih]
  simp [readUnary,h,List.drop_append]

noncomputable def trialNormalize (bs : List Bool) : (ℕ × ℕ) × BitFormula :=
  let x := readUnary bs
  let y := readUnary x.2
  ((x.1,y.1),minimizeList (parseFormula y.2))

noncomputable def trialNormalizeProgram : PolyProgram (List Bool) ((ℕ × ℕ) × BitFormula) trialNormalize := by
  let j := PolyProgram.fst ℕ (List Bool)
  let second := (PolyProgram.snd ℕ (List Bool)).comp PolyProgram.readUnary
  let k := second.comp (PolyProgram.fst ℕ (List Bool))
  let F := (second.comp (PolyProgram.snd ℕ (List Bool))).comp normalizeProgram
  exact PolyProgram.readUnary.comp ((j.pair k).pair F)

lemma trialNormalize_encode {N : ℕ} (j k : ℕ) (F : Formula N) :
    trialNormalize (trialInput j k (encodeFormula F))=((j,k),minimizeList F.bitList) := by
  simp only [trialNormalize,trialInput,readUnary_encode,←Formula.bitList_parse]


end ParityWL.Complexity

end OAI
