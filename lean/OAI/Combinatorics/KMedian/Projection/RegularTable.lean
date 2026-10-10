import Mathlib
import OAI.Combinatorics.KMedian.Projection.CodingLaws
import OAI.Combinatorics.KMedian.Projection.RepairProgram
import OAI.Combinatorics.KMedian.Projection.RowsBuild

namespace OAI

section Inline_PCPProjectionRegularTable
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram ProjectionTable
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] [Coding A] [Hardcoded A]
noncomputable def edgeSource (t : CSPTable A) (v : ℕ) (s : Port×Bool) : ℕ×Port :=
  SeedCombinators.source (rotate (A:=A)) t v s
omit [DecidableEq A] [Inhabited A] [Coding A] [Hardcoded A] in
lemma poly_edgeSource : Poly (fun z : (CSPTable A×ℕ)×(Port×Bool) =>edgeSource z.1.1 z.1.2 z.2) := by
  unfold edgeSource
  with_reducible exact SeedCombinators.poly_source (T:=CSPTable A) (D:=Port) (rotate (A:=A)) (poly_rotate (A:=A))

noncomputable def edgeProject (t : CSPTable A) (v : ℕ) (s : Port×Bool) : (A×A)→A := fun a =>
  SeedCombinators.project (rotate (A:=A)) (repair (A:=A)) t v s a
lemma poly_edgeProject : Poly (fun z : (CSPTable A×ℕ)×(Port×Bool) =>edgeProject z.1.1 z.1.2 z.2) := by
  unfold edgeProject
  with_reducible exact SeedCombinators.poly_project (T:=CSPTable A) (D:=Port) (A:=A) (rotate (A:=A)) (repair (A:=A)) (poly_rotate (A:=A)) (poly_repair (A:=A))

noncomputable def edgeRow (t : CSPTable A) (v : ℕ) (s : Port×Bool) : ProjectionRow (A×A) A :=
  SeedCombinators.numbered (rotate (A:=A)) (repair (A:=A)) (fun d : Port=>(Fintype.equivFin Port d).val)
    (Fintype.card Port) t v s
lemma poly_edgeRow : Poly (fun z : (CSPTable A×ℕ)×(Port×Bool) =>edgeRow z.1.1 z.1.2 z.2) := by
  have hi : Poly (fun d : Port=>(Fintype.equivFin Port d).val) := hardcoded _
  unfold edgeRow
  with_reducible exact (SeedCombinators.poly_numbered (T:=CSPTable A) (D:=Port) (A:=A)
    (rotate (A:=A)) (repair (A:=A)) _ _ (poly_rotate (A:=A)) (poly_repair (A:=A)) hi)

noncomputable def regularTable (t : CSPTable A) : ProjectionTable (A×A) A :=
  ((global t).flatMap (fun _=>List.replicate (Fintype.card Port) ()),
    (List.range (global t).length).map (fun v => (Ordered.fixed (Port×Bool)).entries.map (edgeRow t v)))
lemma poly_regularTable : Poly (regularTable (A:=A)) := by
  unfold regularTable
  apply Poly.pair
  · exact Poly.list_flatMap (Automatic.Poly.const _) (poly_global (A:=A))
  · exact Poly.list_map (Poly.list_map (poly_edgeRow (A:=A)) (Automatic.Poly.const _)) (Poly.list_indices.comp (poly_global (A:=A)))

variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable abbrev nodeEquiv := ExpanderFamily.vertexEquiv (GlobalRegularization.depth (CloudSpec.C t h))
noncomputable def nodeOrder : Ordered (GlobalRegularization.Node (CloudSpec.C t h)) :=
  (Ordered.fin _).map (nodeEquiv t h).symm
noncomputable def rootEquiv := ((nodeEquiv t h).prodCongr (Fintype.equivFin Port)).trans finProdFinEquiv
noncomputable def projection := (CloudSpec.regularCSP t h).projection
  (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2)
omit [Coding A] [Hardcoded A] in
lemma edgeSource_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (s : Port×Bool) :
    edgeSource t (CloudSpec.vertexCode t h v) s=
      (CloudSpec.vertexCode t h ((projection t h).edge.symm (v,s)).1.1,((projection t h).edge.symm (v,s)).1.2) := by
  have hh := (SeedCombinators.source_correct (CloudSpec.regularGraph t h) (CloudSpec.regularCSP t h)
    (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2) (rotate (A:=A)) t (CloudSpec.vertexCode t h)
    (fun v d=>by simpa only [PortGraph.step,PortGraph.back] using CloudSpec.rotate_correct t h v d) v s)
  simpa only [edgeSource,projection] using hh

omit [Coding A] [Hardcoded A] in
lemma edgeRow_correct (v : GlobalRegularization.Node (CloudSpec.C t h)) (s : Port×Bool) :
    edgeRow t (CloudSpec.vertexCode t h v) s=
      ((rootEquiv t h ((projection t h).edge.symm (v,s)).1).val,(projection t h).project ((projection t h).edge.symm (v,s))) := by
  have hh := (SeedCombinators.numbered_correct (CloudSpec.regularGraph t h) (CloudSpec.regularCSP t h)
    (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2) (rotate (A:=A)) (repair (A:=A)) t
    (nodeEquiv t h) (Fintype.equivFin Port) (fun v d=>by simpa only [nodeEquiv,CloudSpec.vertexCode,PortGraph.step,PortGraph.back] using CloudSpec.rotate_correct t h v d) (fun v d a=>by simpa only [nodeEquiv,CloudSpec.vertexCode] using repair_correct t h v d a) v s)
  simpa only [edgeRow,rootEquiv,nodeEquiv,CloudSpec.vertexCode,projection] using hh

omit [Coding A] [Hardcoded A] in
lemma regularTable_build : regularTable t=build (projection t h) (rootEquiv t h) (nodeOrder t h) (Ordered.fixed (Port×Bool)) := by
  have hh := rows_build (projection t h) (m:=(Fintype.card ExpanderFamily.Branch)^(GlobalRegularization.depth (CloudSpec.C t h)))
    (k:=Fintype.card Port) (rootEquiv t h) (nodeEquiv t h) (Ordered.fixed (Port×Bool))
    (global t) (global_length t h) (edgeRow t)
    (fun v s=>by simpa only [nodeEquiv,CloudSpec.vertexCode] using edgeRow_correct t h v s)
  simpa only [regularTable,nodeOrder] using hh
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRegularTable

end OAI
