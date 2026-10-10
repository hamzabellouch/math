import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListFold
import OAI.Combinatorics.KMedian.Binary.BinaryListMap
import OAI.Combinatorics.KMedian.Binary.BinaryListContext

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

def listBits : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b,false])
  finish _ := []
theorem listBits_run (xs : List Bool) : listBits.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true,b,false]++listBits.run () xs=quote [b]++encodeList encodeBool xs
      rw [ih]
      rfl
end WordTransducer
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def wordAsList : PolyProgram id (encodeList encodeBool) id :=
  WordTransducer.listBits.program.of_word (fun xs => WordTransducer.listBits_run xs)
noncomputable def natAsList : PolyProgram Nat.bits (encodeList encodeBool) Nat.bits :=
  wordAsList.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
noncomputable def natSize : PolyProgram Nat.bits Nat.bits Nat.size :=
  (natAsList.comp (listLength encodeBool false)).congr _ (fun n => Nat.size_eq_bits_len n)
noncomputable def listFlatten (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList (encodeList ea)) (encodeList ea) List.flatten := by
  let P := (listAppend ea a0).listFoldLinear [] 1 (by
    intro bs as
    simp only [EncodedList.append,List.length_append]
    omega)
  exact (((identity (encodeList (encodeList ea))).fanout (constant (encodeList (encodeList ea)) (encodeList ea) [])).comp P).congr _ (fun xs => by
    change xs.foldl (fun b a => b++a) []=xs.flatten
    have he (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => b++a) acc=acc++xs.flatten := by
      induction xs generalizing acc with
      | nil => simp
      | cons y ys hi => simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using hi (acc++y)
    simpa using he xs [])
noncomputable def listFlatMap {f : α → List β} (P : PolyProgram ea (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodeList ea) (encodeList eb) (fun xs => xs.flatMap f) :=
  ((P.listMap a0).comp (listFlatten eb b0)).congr _ (fun xs => by rfl)
noncomputable def listFlatMapWith {f : γ × α → List β} (P : PolyProgram (encodePair ec ea) (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.flatMap (fun a => f (x.1,a))) :=
  ((P.listMapWith a0 []).comp (listFlatten eb b0)).congr _ (fun x => by rfl)
noncomputable def listAllWith {p : γ × α → Bool} (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair ec (encodeList ea)) encodeBool (fun x => x.2.all (fun a => p (x.1,a))) :=
  ((P.listMapWith a0 false).comp (listAll (identity encodeBool) false)).congr _ (fun x => by simp only [Function.comp_apply,List.all_map,Function.id_comp])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
