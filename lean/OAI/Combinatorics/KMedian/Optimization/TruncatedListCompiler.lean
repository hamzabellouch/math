import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListIndices
import OAI.Combinatorics.KMedian.Binary.BinaryListIndex
import OAI.Combinatorics.KMedian.Optimization.TruncatedListOperations
import OAI.Combinatorics.KMedian.Optimization.DualListCompiler

namespace OAI


                                             
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function
abbrev etrunc := encodePair (encodePair ers er) Ratio.encode
abbrev enext := encodePair etrunc (encodePair Ratio.encode Ratio.encode)

noncomputable def truncateRowProgram : PolyProgram (encodePair Ratio.encode er) er (fun x : ℚ × Row => Truncated.row x.2 x.1) := by
  let t := snd Ratio.encode Ratio.encode
  let test := (t.fanout (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1)).comp ratLE
  let coord := ite test (fst Ratio.encode Ratio.encode) t
  exact (coord.listMapWith 0 0).congr _ (fun x => by simp only [Function.comp_apply,decide_eq_true_eq,Truncated.row])

noncomputable def truncateMatrixProgram : PolyProgram (encodePair ers Ratio.encode) ers (fun x : Rows × ℚ => Truncated.matrix x.1 x.2) :=
  ((exchange ers Ratio.encode).comp (truncateRowProgram.listMapWith [] [])).congr _ (fun _ => rfl)

noncomputable def objectiveProgram : PolyProgram etrunc Ratio.encode (fun x : (Rows × Row) × ℚ => Truncated.objective x.1.1 x.1.2 x.2) := by
  let dat := fst (encodePair ers er) Ratio.encode
  let ys := dat.comp (snd ers er)
  let H := snd (encodePair ers er) Ratio.encode
  let matrix := ((dat.comp (fst ers er)).fanout H).comp truncateMatrixProgram
  let ec := encodePair er Ratio.encode
  let c := fst ec er
  let y := c.comp (fst er Ratio.encode)
  let h := c.comp (snd er Ratio.encode)
  let row := snd ec er
  let value := ((row.fanout y).fanout h).comp dualValueProgram
  exact ((((ys.fanout H).fanout matrix).comp (value.listMapWith [] 0)).comp ratSum).congr _ (fun _ => rfl)

noncomputable def componentProgram : PolyProgram (encodePair etrunc Nat.bits) Ratio.encode
    (fun x : ((Rows × Row) × ℚ) × ℕ => Truncated.component x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  let t := fst etrunc Nat.bits
  let dat := t.comp (fst (encodePair ers er) Ratio.encode)
  let ys := dat.comp (snd ers er)
  let H := t.comp (snd (encodePair ers er) Ratio.encode)
  let i := snd etrunc Nat.bits
  let matrix := ((dat.comp (fst ers er)).fanout H).comp truncateMatrixProgram
  let ec := encodePair (encodePair er Ratio.encode) Nat.bits
  let c := fst ec er
  let yh := c.comp (fst (encodePair er Ratio.encode) Nat.bits)
  let y := yh.comp (fst er Ratio.encode)
  let h := yh.comp (snd er Ratio.encode)
  let idx := c.comp (snd (encodePair er Ratio.encode) Nat.bits)
  let row := snd ec er
  let best := ((row.fanout y).fanout h).comp dualBestProgram
  let distance := (row.fanout idx).comp (listGetD Ratio.encode 0)
  let coord := (((best.fanout distance).comp ratSub).comp positivePart).comp ratNeg
  exact (((((ys.fanout H).fanout i).fanout matrix).comp (coord.listMapWith [] 0)).comp ratSum).congr _ (fun _ => rfl)

noncomputable def gradientProgram : PolyProgram etrunc er (fun x : (Rows × Row) × ℚ => Truncated.gradient x.1.1 x.1.2 x.2) := by
  let ys := (fst (encodePair ers er) Ratio.encode).comp (snd ers er)
  let ids := ys.comp (listIndices Ratio.encode 0)
  exact (((identity etrunc).fanout ids).comp (componentProgram.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def nextProgram : PolyProgram enext er
    (fun x : ((Rows × Row) × ℚ) × (ℚ × ℚ) => Truncated.next x.1.1.1 x.1.1.2 x.1.2 x.2.1 x.2.2) := by
  let t := fst etrunc (encodePair Ratio.encode Ratio.encode)
  let kr := snd etrunc (encodePair Ratio.encode Ratio.encode)
  let ys := (t.comp (fst (encodePair ers er) Ratio.encode)).comp (snd ers er)
  let grad := t.comp gradientProgram
  let zip := (ys.fanout grad).comp (listZip Ratio.encode Ratio.encode 0 0)
  let rate := kr.comp (snd Ratio.encode Ratio.encode)
  let coords := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
  let y := coords.comp (fst Ratio.encode Ratio.encode)
  let g := coords.comp (snd Ratio.encode Ratio.encode)
  let rg := ((fst Ratio.encode (encodePair Ratio.encode Ratio.encode)).fanout g).comp ratMul
  let coord := (y.fanout rg).comp ratSub
  let update := (rate.fanout zip).comp (coord.listMapWith (0,0) 0)
  exact ((update.fanout (kr.comp (fst Ratio.encode Ratio.encode))).comp projectProgram).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Program
end

end OAI
