import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListZip
import OAI.Combinatorics.KMedian.Optimization.SimplexListProgram
import OAI.Combinatorics.KMedian.Optimization.DualListOperations

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function
abbrev epoint := encodePair er er
abbrev edual := encodePair epoint Ratio.encode

noncomputable def maximumProgram : PolyProgram er Ratio.encode maximum :=
  (((identity er).fanout (listHead Ratio.encode 0)).comp maxFold).congr _ (fun _ => rfl)

noncomputable def candidatesProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => Dual.candidates x.1 x.2) := by
  let consH := (exchange er Ratio.encode).comp (listCons Ratio.encode)
  exact (((constant (encodePair er Ratio.encode) Ratio.encode 0).fanout consH).comp (listCons Ratio.encode)).congr _ (fun _ => rfl)

noncomputable def dualAffineProgram : PolyProgram edual Ratio.encode (fun x : (Row × Row) × ℚ => Dual.affine x.1.1 x.1.2 x.2) := by
  let t := snd epoint Ratio.encode
  let zip := (fst epoint Ratio.encode).comp (listZip Ratio.encode Ratio.encode 0 0)
  let ec := encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)
  let q := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
  let d := q.comp (fst Ratio.encode Ratio.encode)
  let y := q.comp (snd Ratio.encode Ratio.encode)
  let s := ((fst Ratio.encode (encodePair Ratio.encode Ratio.encode)).fanout d).comp ratSub
  let weighted := (y.fanout (s.comp positivePart)).comp ratMul
  let sum := (((t.fanout zip).comp (weighted.listMapWith (0,0) 0)).comp ratSum)
  exact ((t.fanout sum).comp ratSub).congr _ (fun _ => rfl)

noncomputable def dualValueProgram : PolyProgram edual Ratio.encode (fun x : (Row × Row) × ℚ => Dual.value x.1.1 x.1.2 x.2) := by
  let dat := fst epoint Ratio.encode
  let ts := (((dat.comp (fst er er)).fanout (snd epoint Ratio.encode)).comp candidatesProgram)
  exact (((dat.fanout ts).comp (dualAffineProgram.listMapWith 0 0)).comp maximumProgram).congr _ (fun _ => rfl)

noncomputable def dualBestProgram : PolyProgram edual Ratio.encode (fun x : (Row × Row) × ℚ => Dual.best x.1.1 x.1.2 x.2) := by
  let dat := fst epoint Ratio.encode
  let ts := (((dat.comp (fst er er)).fanout (snd epoint Ratio.encode)).comp candidatesProgram)
  let context := dat.fanout dualValueProgram
  let c := fst edual Ratio.encode
  let dy := c.comp (fst epoint Ratio.encode)
  let v := c.comp (snd epoint Ratio.encode)
  let a := snd edual Ratio.encode
  let test := (((dy.fanout a).comp dualAffineProgram).fanout v).comp ratEQ
  exact (((context.fanout ts).comp (test.listFilterWith 0 (([],[]),0))).comp maximumProgram).congr _ (fun _ => rfl)

noncomputable def dualGradientProgram : PolyProgram edual er (fun x : (Row × Row) × ℚ => Dual.gradient x.1.1 x.1.2 x.2) := by
  let ds := (fst epoint Ratio.encode).comp (fst er er)
  let coord := (ratSub.comp positivePart).comp ratNeg
  exact ((dualBestProgram.fanout ds).comp (coord.listMapWith 0 0)).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Program
end

end OAI
