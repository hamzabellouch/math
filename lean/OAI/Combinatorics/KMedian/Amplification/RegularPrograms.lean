import Mathlib
import OAI.Combinatorics.KMedian.Expanders.CloudPrograms
import OAI.Combinatorics.KMedian.Machines.BlendCompiler
import OAI.Combinatorics.KMedian.Machines.RawSquare
import OAI.Combinatorics.KMedian.PCP.GlobalRegularization

namespace OAI

section Inline_PCPRegularPrograms
namespace MetricKMedian.PCP.Compiler.RegularProgram
open Binary Binary.Automatic CloudProgram RotationTable
open scoped Classical

variable {A : Type} [Fintype A]
abbrev RPort := CloudCopies.RegularPort
abbrev Port := GlobalRegularization.Degree
@[fun_prop] lemma poly_zeroBranch : Poly (fun i : Fin 3 => decide (i=0)) := hardcoded _
noncomputable def matchStep (t : CSPTable A) (p : ℕ × ℕ) : ℕ × ℕ :=
  let ds := incident t p.1
  if p.2<ds.length then
    let d := ds[p.2]?.getD (0,false)
    let e := (d.1,!d.2)
    let v := endpoint t e
    (v,dartIndex t v e)
  else p
noncomputable def matchAllowed (t : CSPTable A) (p : ℕ × ℕ) : Finset (A × A) :=
  let ds := incident t p.1
  if p.2<ds.length then
    let d := ds[p.2]?.getD (0,false)
    let rel := (CSPTable.row t d.1).2.2
    if d.2 then rel.image Prod.swap else rel
  else Finset.univ
noncomputable def localRotate (t : CSPTable A) (p : ℕ × ℕ) (d : RPort) : (ℕ × ℕ) × RPort :=
  if d.1=0 then (matchStep t p,d) else
    let q := lookup (cloud t p.1) p.2 d.2.2
    ((p.1,q.1),(d.1,(d.2.1,q.2)))
noncomputable def localAllowed (t : CSPTable A) (p : ℕ × ℕ) (d : RPort) : Finset (A × A) :=
  if d.1=0 then matchAllowed t p else Finset.univ.filter (fun a => a.1=a.2)
noncomputable def paddedRotate (t : CSPTable A) (v : ℕ) (d : RPort) : ℕ × RPort :=
  if v<(nodes t).length then
    let p := (nodes t)[v]?.getD (0,0)
    let q := localRotate t p d
    (index t q.1,q.2)
  else (v,d)
noncomputable def paddedAllowed (t : CSPTable A) (v : ℕ) (d : RPort) : Finset (A × A) :=
  if v<(nodes t).length then localAllowed t ((nodes t)[v]?.getD (0,0)) d else Finset.univ
noncomputable def strongRotate (t : CSPTable A) (v : ℕ) (d : GlobalRegularization.StrongPort) : ℕ × GlobalRegularization.StrongPort :=
  RotationTable.fourthLookup (global t) v d
noncomputable def rotate (t : CSPTable A) (v : ℕ) (d : Port) : ℕ × Port :=
  if d.1=0 then
    let q := paddedRotate t v d.2.1
    (q.1,(d.1,(q.2,d.2.2)))
  else
    let q := strongRotate t v d.2.2
    (q.1,(d.1,(d.2.1,q.2)))
noncomputable def allowed (t : CSPTable A) (v : ℕ) (d : Port) : Finset (A × A) :=
  if d.1=0 then paddedAllowed t v d.2.1 else Finset.univ
@[fun_prop] lemma poly_matchStep : Poly (fun s : CSPTable A × (ℕ × ℕ) => matchStep s.1 s.2) := by
  unfold matchStep
  dsimp only
  apply Poly.ite_prop
  · fun_prop
  · let f : CSPTable A × (ℕ × ℕ) → Dart := fun x =>
      let d := (incident x.1 x.2.1)[x.2.2]?.getD (0,false)
      (d.1,!d.2)
    have hf : Poly f := by unfold f; fun_prop
    have he : Poly (fun x : CSPTable A × (ℕ × ℕ) => endpoint x.1 (f x)) :=
      poly_endpoint.comp (Poly.pair Poly.fst hf)
    have hi := poly_dartIndex.comp (Poly.pair (Poly.pair Poly.fst he) hf)
    exact Poly.pair he hi
  · fun_prop
@[fun_prop] lemma poly_matchAllowed : Poly (fun s : CSPTable A × (ℕ × ℕ) => matchAllowed s.1 s.2) := by
  have ht : Poly (fun r : Finset (A × A) => r.image Prod.swap) := hardcoded _
  have hr := CSPTable.poly_row (A := A)
  unfold matchAllowed
  fun_prop
@[fun_prop] lemma poly_localRotate : Poly (fun s : (CSPTable A × (ℕ × ℕ)) × RPort => localRotate s.1.1 s.1.2 s.2) := by
  unfold localRotate
  dsimp only
  apply Poly.ite_prop
  · exact poly_zeroBranch.comp (Poly.fst.comp Poly.snd)
  · have hm := poly_matchStep (A := A)
    fun_prop
  · have hl := RotationTable.poly_lookup (D := ExpanderFamily.Degree)
    fun_prop
@[fun_prop] lemma poly_localAllowed : Poly (fun s : (CSPTable A × (ℕ × ℕ)) × RPort => localAllowed s.1.1 s.1.2 s.2) := by
  unfold localAllowed
  apply Poly.ite_prop
  · exact poly_zeroBranch.comp (Poly.fst.comp Poly.snd)
  · exact poly_matchAllowed.comp (by fun_prop)
  · exact Automatic.Poly.const _
@[fun_prop] lemma poly_paddedRotate : Poly (fun s : (CSPTable A × ℕ) × RPort => paddedRotate s.1.1 s.1.2 s.2) := by
  unfold paddedRotate
  dsimp only
  apply Poly.ite_prop
  · fun_prop
  · have hp : Poly (fun x : (CSPTable A × ℕ) × RPort => ((nodes x.1.1)[x.1.2]?.getD (0,0))) := by fun_prop
    have hl := poly_localRotate.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) hp) Poly.snd)
    exact Poly.pair (poly_index.comp (Poly.pair (Poly.fst.comp Poly.fst) (Poly.fst.comp hl))) (Poly.snd.comp hl)
  · fun_prop
@[fun_prop] lemma poly_paddedAllowed : Poly (fun s : (CSPTable A × ℕ) × RPort => paddedAllowed s.1.1 s.1.2 s.2) := by
  unfold paddedAllowed
  apply Poly.ite_prop
  · fun_prop
  · have hp : Poly (fun x : (CSPTable A × ℕ) × RPort => ((nodes x.1.1)[x.1.2]?.getD (0,0))) := by fun_prop
    exact poly_localAllowed.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) hp) Poly.snd)
  · exact Automatic.Poly.const _
@[fun_prop] lemma poly_strongRotate : Poly (fun s : (CSPTable A × ℕ) × GlobalRegularization.StrongPort => strongRotate s.1.1 s.1.2 s.2) := by
  unfold strongRotate
  apply RotationTable.poly_fourthLookup_comp (D := ExpanderFamily.Degree)
  · exact poly_global.comp (Poly.fst.comp Poly.fst)
  · exact Poly.snd.comp Poly.fst
  · exact Poly.snd
@[fun_prop] lemma poly_rotate : Poly (fun s : (CSPTable A × ℕ) × Port => rotate s.1.1 s.1.2 s.2) := by
  exact poly_blendProgram (fun p : CSPTable A × ℕ => paddedRotate p.1 p.2)
    (fun p : CSPTable A × ℕ => strongRotate p.1 p.2) poly_paddedRotate poly_strongRotate
@[fun_prop] lemma poly_allowed : Poly (fun s : (CSPTable A × ℕ) × Port => allowed s.1.1 s.1.2 s.2) := by
  unfold allowed
  apply Poly.ite_prop
  · exact poly_zeroBranch.comp (Poly.fst.comp Poly.snd)
  · exact poly_paddedAllowed.comp (Poly.pair Poly.fst (Poly.fst.comp (Poly.snd.comp Poly.snd)))
  · exact Automatic.Poly.const _
end MetricKMedian.PCP.Compiler.RegularProgram

end Inline_PCPRegularPrograms

end OAI
