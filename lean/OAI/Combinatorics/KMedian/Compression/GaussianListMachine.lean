import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListMap
import OAI.Combinatorics.KMedian.Compression.GaussianListCompiler
import OAI.Combinatorics.KMedian.Binary.BooleanSum

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function
abbrev Frame := ℕ × Row
abbrev Frames := List Frame
abbrev Desc := (List Unit × Rows) × Frames
abbrev Up := Row × Frames
abbrev State := Desc ⊕ Up
abbrev efs := encodeList ef
abbrev edata := encodePair eslots ers
abbrev ed := encodePair edata efs
abbrev eUp := encodePair er efs
abbrev eState : State → List Bool := encodeLoop eUp ed

def down (d : Desc) : Row ⊕ State :=
  if d.1.2.isEmpty then .inr (.inr (basis d.1.1,d.2))
  else if d.1.1.isEmpty then .inr (.inr ([],d.2))
  else
    let row := d.1.2.head?.getD []
    let p := pivot row
    if p<row.length then
      .inr (.inl ((d.1.1.tail,residual row p d.1.2.tail),(p,row)::d.2))
    else .inr (.inl ((d.1.1,d.1.2.tail),d.2))

def up (u : Up) : Row ⊕ State :=
  if u.2.isEmpty then .inl u.1
  else
    let f := u.2.head?.getD (0,[])
    .inr (.inr (lift f.2 f.1 u.1,u.2.tail))

def body : State → Row ⊕ State := Sum.elim down up

noncomputable def downProgram : PolyProgram ed (encodeLoop eState er) down := by
  let dat := fst edata efs
  let slots := dat.comp (fst eslots ers)
  let rows := dat.comp (snd eslots ers)
  let frames := snd edata efs
  let row := rows.comp (listHead er [])
  let p := row.comp pivotProgram
  let frame := p.fanout row
  let tl := rows.comp (listTail er [])
  let recRows := (frame.fanout tl).comp residualProgram
  let recSlots := slots.comp (listTail eu ())
  let recFrames := (frame.fanout frames).comp (listCons ef)
  let recurse := (((recSlots.fanout recRows).fanout recFrames).comp (injectLeft eUp ed)).comp (injectRight eState er)
  let skip := (((slots.fanout tl).fanout frames).comp (injectLeft eUp ed)).comp (injectRight eState er)
  let test := (p.fanout (row.comp (listLength Ratio.encode 0))).comp natLT
  let pivotCase := ite test skip recurse
  let zeroCase := (((constant ed er []).fanout frames).comp (injectRight eUp ed)).comp (injectRight eState er)
  let noCols := ite (slots.comp (listIsEmpty eu)) pivotCase zeroCase
  let baseCase := (((slots.comp basisProgram).fanout frames).comp (injectRight eUp ed)).comp (injectRight eState er)
  exact (ite (rows.comp (listIsEmpty er)) noCols baseCase).congr _ (fun x => by
    simp only [down,Function.comp_def,decide_eq_true_eq])

noncomputable def upProgram : PolyProgram eUp (encodeLoop eState er) up := by
  let z := fst er efs
  let frames := snd er efs
  let frame := frames.comp (listHead ef (0,[]))
  let new := (frame.fanout z).comp liftProgram
  let tl := frames.comp (listTail ef (0,[]))
  let recur := ((new.fanout tl).comp (injectRight eUp ed)).comp (injectRight eState er)
  let done := z.comp (injectLeft eState er)
  exact (ite (frames.comp (listIsEmpty ef)) recur done).congr _ (fun _ => rfl)

noncomputable def bodyProgram : PolyProgram eState (encodeLoop eState er) body :=
  sumElim ed eUp downProgram upProgram (([],[]),[]) ([],[])
end MetricKMedian.Gaussian.ListOperation
end

end OAI
