import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryWords

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
def pack : Transducer where
  Q := Unit
  initial := ()
  next := fun _ b => ((),[true,b,false])
  finish := fun _ => []
 theorem pack_run (xs : List Bool) : pack.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,pack,encodeList,encodeBool,quote,List.append_assoc,List.nil_append] using congrArg (fun ys => [true,b,false]++ys) ih
inductive Phase | start | value | stop deriving DecidableEq
instance : Fintype Phase := ⟨{.start,.value,.stop},by intro p; cases p <;> simp⟩
def unpack : Transducer where
  Q := Phase
  initial := .start
  next := fun q b => match q with
    | .start => (.value,[])
    | .value => (.stop,[b])
    | .stop => (.start,[])
  finish := fun _ => []
 theorem unpack_run (xs : List Bool) : unpack.run .start (encodeList encodeBool xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [encodeList,encodeBool,quote,List.cons_append,List.nil_append,Transducer.run,unpack,List.append_assoc,List.singleton_append] using congrArg (List.cons b) ih
noncomputable def packProgram : PolyProgram id (encodeList encodeBool) (id : List Bool → List Bool) :=
  pack.program.recode id (fun _ => rfl) (fun xs => pack_run xs)
noncomputable def unpackProgram : PolyProgram (encodeList encodeBool) id (id : List Bool → List Bool) :=
  unpack.program.recode (encodeList encodeBool) (fun _ => rfl) (fun xs => unpack_run xs)
noncomputable def valueProgram : PolyProgram (encodeList encodeBool) Nat.bits Word.value := unpackProgram.comp PolyProgram.toBits
 theorem length (xs : List Bool) : (encodeList encodeBool xs).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [EncodedList.cons_length,encodeBool,List.length_cons,List.length_nil,ih]; omega
end BooleanLists
end MetricKMedian.Binary
end

end OAI
