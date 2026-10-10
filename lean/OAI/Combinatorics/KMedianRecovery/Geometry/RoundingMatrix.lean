import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2
import OAI.Combinatorics.KMedianRecovery.Geometry.RoundingArithmetic

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def round (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) (i j : Fin n) : ℚ :=
  if i=j then 0 else (min cap (max 1 ⌈δ i j/u⌉₊):ℕ)
def pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryRational.encode u,cap.bits]
def ctx : List Bool→List Bool := extractPrefix ∘ extractPrefix
def rowIndex : List Bool→List Bool := discardPrefix ∘ extractPrefix
def colIndex : List Bool→List Bool := discardPrefix
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def rowIndex_computes : PolyComputes rowIndex := extractPrefix_computes.comp discardPrefix_computes
noncomputable def colIndex_computes : PolyComputes colIndex := discardPrefix_computes
noncomputable def distance (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (field 0 (ctx x),rowIndex x),colIndex x))
noncomputable def distance_computes : PolyComputes distance := by
  unfold distance
  have computes := (((ctx_computes.comp (field_computes 0)).pair rowIndex_computes).pair colIndex_computes).comp MetricTable.get_computes
  simpa only [Function.comp_def] using computes
noncomputable def entryInput (x : List Bool) : List Bool := encode [distance x,field 2 (ctx x),field 3 (ctx x)]
noncomputable def entryInput_computes : PolyComputes entryInput :=
  list_computes [distance,field 2 ∘ ctx,field 3 ∘ ctx] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨distance_computes⟩
    · exact ⟨ctx_computes.comp (field_computes 2)⟩
    · exact ⟨ctx_computes.comp (field_computes 3)⟩)
noncomputable def entry (x : List Bool) : List Bool :=
  if value (rowIndex x)=value (colIndex x) then BinaryRational.encode 0 else BinaryRound.rational (entryInput x)
noncomputable def entry_computes : PolyComputes entry := by
  change PolyComputes (fun x=>if value (rowIndex x)=value (colIndex x) then BinaryRational.encode 0 else BinaryRound.rational (entryInput x))
  simpa only [decide_eq_true_eq,Function.comp_def] using
    (NatOps.eq rowIndex_computes colIndex_computes).cond (const_computes (BinaryRational.encode 0))
      (entryInput_computes.comp BinaryRound.rational_computes)
lemma entry_pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) (i j : Fin n) :
    entry (pairBits (pairBits (pack δ u cap,i.val.bits),j.val.bits))=BinaryRational.encode (round δ u cap i j) := by
  simp only [entry,rowIndex,colIndex,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
  by_cases hij : i=j
  · simp only [hij,ite_true,round]
  · have hv : i.val≠j.val := fun he=>hij (Fin.ext he)
    rw [ite_eq_right hv,round,ite_eq_right hij]
    have he : entryInput (pairBits (pairBits (pack δ u cap,i.val.bits),j.val.bits))=BinaryRound.pack (δ i j) u cap := by
      simp only [entryInput,distance,ctx,rowIndex,colIndex,Function.comp_apply,extractPrefix_pairBits,
        discardPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.getD_some,BinaryRound.pack]
      rw [show MetricTable.get (pairBits (pairBits (RationalMatrix.encode δ,i.val.bits),j.val.bits))=BinaryRational.encode (δ i j) from MetricTable.get_pack δ i j]
    rw [he,BinaryRound.rational_pack]
noncomputable def row (x : List Bool) : List Bool :=
  mapWith entry (pairBits (x,BinaryEllipsoidInitial.indices (field 1 (extractPrefix x))))
noncomputable def row_computes : PolyComputes row := by
  unfold row
  have computes := (id_computes.pair ((extractPrefix_computes.comp (field_computes 1)).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes entry_computes)
  simpa only [Function.comp_def,id_eq] using computes
lemma row_pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) (i : Fin n) :
    row (pairBits (pack δ u cap,i.val.bits))=RationalMatrix.rowEncode (round δ u cap i) := by
  simp only [row,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.getD_some,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn]
  change encode (List.ofFn (fun j : Fin n=>entry (pairBits (pairBits (pack δ u cap,i.val.bits),j.val.bits))))=_
  simp only [entry_pack,RationalMatrix.rowEncode_eq]
noncomputable def run (x : List Bool) : List Bool :=
  mapWith row (pairBits (x,BinaryEllipsoidInitial.indices (field 1 x)))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (id_computes.pair ((field_computes 1).comp BinaryEllipsoidInitial.indices_computes)).comp (mapWith_computes row_computes)
  simpa only [Function.comp_def,id_eq] using computes
lemma run_pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) :
    run (pack δ u cap)=RationalMatrix.encode (round δ u cap) := by
  simp only [run,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn]
  change encode (List.ofFn (fun i : Fin n=>row (pairBits (pack δ u cap,i.val.bits))))=_
  simp only [row_pack,RationalMatrix.encode]
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
