import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListIndices
import OAI.Combinatorics.KMedian.Compression.AffineListOperations

namespace OAI


                                          
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def entriesProgram : PolyProgram ed ees entries := by
  let zz := encodePair Signed.encode er
  let zip := (snd es (encodePair er em)).comp (listZip Signed.encode er 0 [])
  exact (zip.comp (((listIndices zz (0,[])).fanout (identity (encodeList zz))).comp (listZip Nat.bits zz 0 (0,[])))).congr _ (fun _ => rfl)

noncomputable def activeProgram : PolyProgram ed ees active := by
  let num := (snd Nat.bits (encodePair Signed.encode er)).comp (fst Signed.encode er)
  let test := ((num.fanout (constant ee Signed.encode 0)).comp intEQ).comp boolNot
  exact (entriesProgram.comp (test.listFilter (0,(0,[])))).congr _ (fun x => by
    simp only [Function.comp_apply,active]
    congr 1
    funext e
    simp)

noncomputable def activeRowsProgram : PolyProgram ed em activeRows := by
  let ones := activeProgram.comp ((constant ee Signed.encode 1).listMap (0,(0,[])))
  let ids := (fst es (encodePair er em)).comp (listIndices Gaussian.ListOperation.eu ())
  let a := fst Nat.bits ee
  let row := (snd Nat.bits ee).comp ((snd Nat.bits (encodePair Signed.encode er)).comp (snd Signed.encode er))
  let coord := (row.fanout a).comp (listGetD Signed.encode 0)
  let col := (exchange ees Nat.bits).comp (coord.listMapWith (0,(0,[])) 0)
  let cols := (activeProgram.fanout ids).comp (col.listMapWith 0 [])
  exact ((ones.fanout cols).comp (listCons er)).congr _ (fun _ => rfl)

noncomputable def activeDataProgram : PolyProgram ed Gaussian.IntegerProgram.ed activeData :=
  (((activeProgram.comp ((constant ee Gaussian.ListOperation.eu ()).listMap (0,(0,[])))).fanout activeRowsProgram)).congr _ (fun _ => rfl)

noncomputable def kernelInputProgram : PolyProgram Input.encode Gaussian.IntegerProgram.Input.encode Input.kernel :=
  activeDataProgram.recode Input.raw (fun _ => rfl) (fun I => by rw [activeData_raw])

abbrev ez := encodePair Nat.bits Signed.encode
noncomputable def extendProgram : PolyProgram (encodePair (encodeList ez) Nat.bits) Signed.encode
    (fun x : List (ℕ × ℤ) × ℕ => extend x.1 x.2) := by
  let a := fst Nat.bits ez
  let b := (snd Nat.bits ez).comp (fst Nat.bits Signed.encode)
  let test := (b.fanout a).comp natEQ
  let filtered := (exchange (encodeList ez) Nat.bits).comp (test.listFilterWith (0,0) 0)
  exact ((filtered.comp ((snd Nat.bits Signed.encode).listMap (0,0))).comp IntegerList.sumProgram).congr _ (fun _ => rfl)

noncomputable def fullProgram : PolyProgram (encodePair ed er) er (fun x : Data × Row => full x.1 x.2) := by
  let x := fst ed er
  let z := snd ed er
  let ids := ((x.comp activeProgram).comp ((fst Nat.bits (encodePair Signed.encode er)).listMap (0,(0,[]))))
  let zs := (ids.fanout z).comp (listZip Nat.bits Signed.encode 0 0)
  let out := ((x.comp (snd es (encodePair er em))).comp (fst er em)).comp (listIndices Signed.encode 0)
  exact ((zs.fanout out).comp (extendProgram.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def affineKernelProgram : PolyProgram Input.encode er (fun I => List.ofFn (computedAffineKernel I.μ I.v)) := by
  let raw : PolyProgram Input.encode ed Input.raw := (identity ed).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let kern := kernelInputProgram.comp Gaussian.IntegerProgram.kernelProgram
  exact ((raw.fanout kern).comp fullProgram).congr _ (fun I => full_raw I)

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
