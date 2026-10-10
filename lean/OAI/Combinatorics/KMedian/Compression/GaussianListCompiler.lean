import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryPredicates
import OAI.Combinatorics.KMedian.Binary.BinaryListIndex
import OAI.Combinatorics.KMedian.Binary.BinaryListContext
import OAI.Combinatorics.KMedian.Binary.BinaryListSelection
import OAI.Combinatorics.KMedian.Binary.BinaryRationalFold
import OAI.Combinatorics.KMedian.Binary.BinaryListZip
import OAI.Combinatorics.KMedian.Compression.GaussianListOperations

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function
abbrev er : Row → List Bool := encodeList Ratio.encode
abbrev ers : Rows → List Bool := encodeList er
abbrev ef : ℕ × Row → List Bool := encodePair Nat.bits er
abbrev eu : Unit → List Bool := fun _ => []
abbrev eslots : List Unit → List Bool := encodeList eu

noncomputable def pivotProgram : PolyProgram er Nat.bits pivot :=
  (ratNonzero.listFindIdx 0).congr _ (fun _ => rfl)

noncomputable def coefficientsProgram : PolyProgram ef er (fun x : ℕ × Row => coefficients x.2 x.1) := by
  let p := fst Nat.bits er
  let row := snd Nat.bits er
  let inp := row.fanout p
  let denom := inp.comp (listGetD Ratio.encode 0)
  let rem := inp.comp (listEraseIdx Ratio.encode 0)
  let divide : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.2/x.1) :=
    ((exchange Ratio.encode Ratio.encode).comp ratDiv).congr _ (fun _ => rfl)
  exact ((denom.fanout rem).comp (divide.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def reduceProgram : PolyProgram (encodePair (encodePair er Nat.bits) er) er
    (fun x : (Row × ℕ) × Row => reduce x.1.1 x.1.2 x.2) := by
  let ec := encodePair er Nat.bits
  let cp := fst ec er
  let c := cp.comp (fst er Nat.bits)
  let p := cp.comp (snd er Nat.bits)
  let row := snd ec er
  let inp := row.fanout p
  let rem := inp.comp (listEraseIdx Ratio.encode 0)
  let val := inp.comp (listGetD Ratio.encode 0)
  let zp := (rem.fanout c).comp (listZip Ratio.encode Ratio.encode 0 0)
  let term : PolyProgram (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)) Ratio.encode
      (fun x : ℚ × (ℚ × ℚ) => x.2.1-x.2.2*x.1) := by
    let pair := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
    let a := pair.comp (fst Ratio.encode Ratio.encode)
    let b := pair.comp (snd Ratio.encode Ratio.encode)
    let d := fst Ratio.encode (encodePair Ratio.encode Ratio.encode)
    exact ((a.fanout ((b.fanout d).comp ratMul)).comp ratSub).congr _ (fun _ => rfl)
  exact ((val.fanout zp).comp (term.listMapWith (0,0) 0)).congr _ (fun _ => rfl)

noncomputable def residualProgram : PolyProgram (encodePair ef ers) ers
    (fun x : (ℕ × Row) × Rows => residual x.1.2 x.1.1 x.2) := by
  let frame := fst ef ers
  let p := frame.comp (fst Nat.bits er)
  let c := frame.comp coefficientsProgram
  let rows := snd ef ers
  let start := (c.fanout p).fanout rows
  exact (start.comp (reduceProgram.listMapWith [] [])).congr _ (fun _ => rfl)

noncomputable def liftProgram : PolyProgram (encodePair ef er) er
    (fun x : (ℕ × Row) × Row => lift x.1.2 x.1.1 x.2) := by
  let frame := fst ef er
  let p := frame.comp (fst Nat.bits er)
  let c := frame.comp coefficientsProgram
  let z := snd ef er
  let terms := (c.fanout z).comp (listZipWith Ratio.encode Ratio.encode 0 0 ratMul)
  let value := (terms.comp ratSum).comp ratNeg
  exact (((z.fanout p).fanout value).comp (listInsertAt Ratio.encode 0)).congr _ (fun _ => rfl)

noncomputable def basisProgram : PolyProgram eslots er basis := by
  let tl := listTail eu ()
  let zero : PolyProgram eu Ratio.encode (fun _ : Unit => (0:ℚ)) := constant eu Ratio.encode 0
  let zeros := tl.comp (zero.listMap ())
  let nonnil := (((constant eslots Ratio.encode 1).fanout zeros).comp (listCons Ratio.encode))
  exact (ite (listIsEmpty eu) nonnil (constant eslots er [])).congr _ (fun _ => rfl)
end MetricKMedian.Gaussian.ListOperation
end

end OAI
