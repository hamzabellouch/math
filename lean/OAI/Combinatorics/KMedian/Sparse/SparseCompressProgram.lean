import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm
import OAI.Combinatorics.KMedian.Sparse.SparseListTrim
import OAI.Combinatorics.KMedian.Compression.CompressionBinaryProgram

namespace OAI


                                             
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function
variable {α γ : Type}

noncomputable def rawProgram (ea : α → List Bool) : PolyProgram (encode ea) (ed ea) raw :=
  (identity (ed ea)).recode raw (fun _ => rfl) (fun _ => rfl)

noncomputable def lawProgram (ea : α → List Bool) : PolyProgram (encode ea) el (fun μ => (raw μ).1) :=
  (rawProgram ea).comp (fst el (encodeList ea))
noncomputable def statesProgram (ea : α → List Bool) : PolyProgram (encode ea) (encodeList ea) (fun μ => μ.states.toList) :=
  ((rawProgram ea).comp (snd el (encodeList ea))).congr _ (fun _ => rfl)

def compressInput (d : γ → ℕ) (v : (c : γ) → α → Fin (d c) → ℚ)
    (s : γ × SparseIntegerLaw α) : IntegerLaw.BinaryCompression.RationalInput :=
  ⟨s.2.length,d s.1,s.2.law,fun i => v s.1 s.2.states[i.val]⟩

noncomputable def compressInputProgram (ea : α → List Bool) (ec : γ → List Bool)
    (a0 : α) (_ : γ) (d : γ → ℕ) (v : (c : γ) → α → Fin (d c) → ℚ)
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr (fun x => List.ofFn (v x.1 x.2))) :
    PolyProgram (encodePair ec (encode ea)) IntegerLaw.BinaryCompression.RationalInput.encode (compressInput d v) := by
  let ctx := fst ec (encode ea)
  let μ := snd ec (encode ea)
  let rows := (ctx.fanout (μ.comp (statesProgram ea))).comp (V.listMapWith a0 [])
  let work := (ctx.comp D).fanout ((μ.comp (lawProgram ea)).fanout rows)
  exact work.recode id (fun _ => rfl) (fun x => by
    change IntegerLaw.BinaryCompression.eqd (List.replicate (d x.1) (),
      ((raw x.2).1,x.2.states.toList.map (fun a => List.ofFn (v x.1 a))))=_
    rw [states_list,List.map_ofFn]
    rfl)

noncomputable def compressWith (ea : α → List Bool) (ec : γ → List Bool)
    (a0 : α) (c0 : γ) (d : γ → ℕ) (v : (c : γ) → α → Fin (d c) → ℚ)
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr (fun x => List.ofFn (v x.1 x.2))) :
    PolyProgram (encodePair ec (encode ea)) (encode ea) (fun x => x.2.compressAuto (v x.1)) := by
  let inp := compressInputProgram ea ec a0 c0 d v D V
  let law := inp.comp IntegerLaw.BinaryCompression.rationalCompressProgram
  let states := (snd ec (encode ea)).comp (statesProgram ea)
  let work := (law.fanout states).comp (trimDataProgram ea a0)
  exact work.recode id (fun _ => rfl) (fun x => by
    change ed ea (trimData (raw (⟨x.2.length,x.2.states,
      x.2.law.compressAuto (fun i => v x.1 x.2.states[i.val])⟩ : SparseIntegerLaw α)))=_
    rw [trimData_raw]
    rfl)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
