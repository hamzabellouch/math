import Mathlib
import OAI.Analysis.MatrixSigning.Realization.ScalarRealization
import OAI.Analysis.MatrixSigning.Realization.BinaryNaturalRealization
import OAI.Analysis.MatrixSigning.Machines.DenseFieldCounter
import OAI.Analysis.MatrixSigning.Machines.UnaryLengthMachine

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W29.FixedSequential KS.W03.MachineCombinators

def wordTail : Realizes (id : Word → Word) id List.tail where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W23.LiteralProgram.pop 0
    spec := fun w => by
      have h := KS.W23.LiteralProgram.pop_spec (0 : Fin 1) (io w)
      convert h using 1 <;> (try rfl)
      funext j;fin_cases j;rfl }

abbrev numFieldsCode := prodCode binaryNatCode (fun n => KS.W01.encodeNat n)

def ratFields : Realizes ratCode numFieldsCode
    (fun q => (KS.W01.intPayload q.num,q.den)) :=
  (wordTail.reindex ratCode ratCode (fun _ => rfl)).changeOutput numFieldsCode
    (fun q => (KS.W01.intPayload q.num,q.den)) (by
      intro q
      change (KS.W01.encodeRat q).tail=_
      unfold KS.W01.encodeRat numFieldsCode prodCode PairRoutine.pair
      dsimp only
      cases q.num <;> rfl)

def ratNumBinary : Realizes ratCode binaryNatCode (fun q => KS.W01.intPayload q.num) :=
  ratFields.then (first binaryNatCode (fun n => KS.W01.encodeNat n))

def unframeNat : Realizes KS.W01.encodeNat binaryNatCode id :=
  (first binaryNatCode (fun _ : Unit => ([] : Word))).reindex KS.W01.encodeNat
    (fun n => (n,())) (by intro n;simp [prodCode,PairRoutine.pair,KS.W01.encodeNat])

def ratDenBinary : Realizes ratCode binaryNatCode (fun q => q.den) :=
  (ratFields.then (second binaryNatCode KS.W01.encodeNat)).then unframeNat

def binaryToNat : Realizes binaryNatCode natCode id where
  cost := fun n => 6*n+4*(binaryNatCode n).length+4
  routine := {
    scratch := 2
    program := compose KS.W03.BinaryToUnary.program (CleanRoutine.transfer 1 2 0)
    spec := fun n => by
      have hd := DenseFieldCounter.base_decode_spec n
      have ht := PairRoutine.take_first (natCode n)
      have h := hd.compose ht
      convert h using 1 <;> (try rfl)
      · funext j;fin_cases j <;> rfl
      · simp only [natCode,binaryNatCode,List.length_replicate];omega }

def wordLength : Realizes (id : Word → Word) natCode List.length where
  cost := fun w => 3*w.length+3
  routine := {
    scratch := 2
    program := compose (KS.W28.UnaryLength.program ⟨![0,1,2],by decide⟩)
      (CleanRoutine.transfer 1 2 0)
    spec := fun w => by
      have hd : RunSpec (KS.W28.UnaryLength.program (⟨![0,1,2],by decide⟩ : Fin 3 ↪ Fin 3))
          (io w) (PairRoutine.smallState [] (natCode w.length) []) (w.length+1) := by
        have h := KS.W28.UnaryLength.length_spec
          (⟨![0,1,2],by decide⟩ : Fin 3 ↪ Fin 3) (fun _ => []) w [] []
        convert h using 1 <;> funext j <;> fin_cases j <;>
          simp [io,PairRoutine.smallState,natCode,KS.W28.FixedPositiveSerializer.registers]
      have h := hd.compose (PairRoutine.take_first (natCode w.length))
      convert h using 1 <;> (try rfl); simp only [natCode,List.length_replicate]; omega }

def binarySize : Realizes binaryNatCode natCode Nat.size :=
  (wordLength.reindex binaryNatCode binaryNatCode (fun _ => rfl)).congr
    KS.W01.natPayloadLength_eq_size

def ratDenSize : Realizes ratCode natCode (fun q : ℚ => q.den.size) := ratDenBinary.then binarySize

def ratNumToNat : Realizes ratCode natCode (fun q : ℚ => q.num.toNat) :=
  (((constant ratCode ratCode 0).le (identity ratCode)).ite
    (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).congr (by
      intro q
      change (if decide (0≤q) then KS.W01.intPayload q.num else 0)=q.num.toNat
      have h := @Rat.num_nonneg q
      cases hn : q.num with
      | ofNat n =>
        have hq : 0≤q := h.mp (by rw [hn];exact Int.natCast_nonneg n)
        simp [hq,KS.W01.intPayload]
      | negSucc n =>
        have hq : ¬0≤q := by intro hp;have := h.mpr hp;rw [hn] at this;omega
        simp [hq])

def ratCeil : Realizes ratCode natCode (fun q => ⌈q⌉₊) :=
  ((((identity ratCode).neg.then ratFloor).neg).then ratNumToNat).congr (by
    intro q
    change (-((⌊-q⌋ : ℤ) : ℚ)).num.toNat=⌈q⌉₊
    rw [Int.floor_neg,Int.cast_neg,neg_neg,Rat.num_intCast,Int.ceil_toNat])

end CurrentKS.Realization

end OAI
