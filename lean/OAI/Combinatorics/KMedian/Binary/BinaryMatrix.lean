import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListIndices
import OAI.Combinatorics.KMedian.Binary.BinaryListIndex
import OAI.Combinatorics.KMedian.Binary.BinaryListContext
import OAI.Combinatorics.KMedian.Compression.GaussianListOperations

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace MatrixList
variable {α β : Type}

def transpose (a0 : α) (x : List β × List (List α)) : List (List α) :=
  (List.range x.1.length).map (fun j => x.2.map (fun row => row[j]?.getD a0))

theorem transpose_ofFn {r n : ℕ} (a0 : α) (slots : List β) (hs : slots.length=n)
    (v : Fin r → Fin n → α) :
    transpose a0 (slots,List.ofFn (fun i => List.ofFn (v i))) =
      List.ofFn (fun j => List.ofFn (fun i => v i j)) := by
  have he : List.range n=List.ofFn (fun i : Fin n => i.val) := by
    apply List.ext_getElem <;> intros <;> simp
  simp only [transpose,hs,he,List.map_ofFn,Function.comp_def,Gaussian.ListOperation.get_ofFn]

noncomputable def transposeProgram (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β) :
    PolyProgram (encodePair (encodeList eb) (encodeList (encodeList ea)))
      (encodeList (encodeList ea)) (transpose a0) := by
  let er := encodeList ea
  let em := encodeList er
  let get := (exchange Nat.bits er).comp (listGetD ea a0)
  let col := get.listMapWith [] a0
  let go := (exchange em Nat.bits).comp col
  let inds := (fst (encodeList eb) em).comp (listIndices eb b0)
  exact (((snd (encodeList eb) em).fanout inds).comp (go.listMapWith 0 [])).congr _ (fun _ => rfl)
end MatrixList
end MetricKMedian.Binary
end

end OAI
