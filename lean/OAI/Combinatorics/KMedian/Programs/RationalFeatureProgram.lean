import Mathlib
import OAI.Combinatorics.KMedian.Compression.CompressionListStep
import OAI.Combinatorics.KMedian.Binary.BinaryMatrix

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function
abbrev QRow := List ℚ
abbrev QRows := List QRow
abbrev eqr := encodeList Ratio.encode
abbrev eqm := encodeList eqr
abbrev QData := List Unit × (LawData × QRows)
abbrev eqd := encodePair es (encodePair el eqm)

structure RationalInput where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℚ

def RationalInput.lawData (I : RationalInput) : LawData := (I.μ.denominator,List.ofFn I.μ.numerator)
def RationalInput.features (I : RationalInput) : QRows := List.ofFn (fun i => List.ofFn (I.v i))
def RationalInput.raw (I : RationalInput) : QData := (List.replicate I.d (),(I.lawData,I.features))
abbrev RationalInput.encode (I : RationalInput) := eqd I.raw

def scaledRows (x : QData) : Rows :=
  let columns := MatrixList.transpose (0:ℚ) (x.1,x.2.2)
  let is := columns.map IntegerList.numerators
  MatrixList.transpose (0:ℤ) (x.2.1.2,is)

theorem scaledRows_raw (I : RationalInput) : scaledRows I.raw=
    List.ofFn (fun i => List.ofFn (RationalLaw.scaledFeatures I.v i)) := by
  unfold scaledRows RationalInput.raw RationalInput.features RationalInput.lawData
  rw [MatrixList.transpose_ofFn _ _ (List.length_replicate ..)]
  simp only [List.map_ofFn,Function.comp_def,IntegerList.numerators_ofFn]
  rw [MatrixList.transpose_ofFn _ _ (List.length_ofFn ..)]
  congr 1
  funext i
  congr 1
  funext j
  exact (RationalLaw.scaledFeatures_eq I.v i j).symm

noncomputable def scaledRowsProgram : PolyProgram eqd em scaledRows := by
  let dim := fst es (encodePair el eqm)
  let rest := snd es (encodePair el eqm)
  let rows := rest.comp (snd el eqm)
  let law := rest.comp (fst el eqm)
  let cols := (dim.fanout rows).comp (MatrixList.transposeProgram Ratio.encode Gaussian.ListOperation.eu 0 ())
  let icols := cols.comp (IntegerList.numeratorsProgram.listMap [])
  let nums := law.comp (snd Signed.encode er)
  exact ((nums.fanout icols).comp (MatrixList.transposeProgram Signed.encode Signed.encode 0 0)).congr _ (fun _ => rfl)

def RationalInput.integer (I : RationalInput) : Input := ⟨I.n,I.d,I.μ,RationalLaw.scaledFeatures I.v⟩

noncomputable def integerInputProgram : PolyProgram RationalInput.encode Input.encode RationalInput.integer := by
  let dim := fst es (encodePair el eqm)
  let law := (snd es (encodePair el eqm)).comp (fst el eqm)
  let p := dim.fanout (law.fanout scaledRowsProgram)
  exact p.recode RationalInput.raw (fun _ => rfl) (fun I => by
    change ed (List.replicate I.d (), (I.lawData, scaledRows I.raw))=_
    rw [scaledRows_raw]
    rfl)
end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
