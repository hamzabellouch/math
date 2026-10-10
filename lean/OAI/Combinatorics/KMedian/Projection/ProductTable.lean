import Mathlib
import OAI.Combinatorics.KMedian.Machines.OrderedLists
import OAI.Combinatorics.KMedian.Machines.UnaryPolynomial
import OAI.Combinatorics.KMedian.Projection.Product
import OAI.Combinatorics.KMedian.Projection.Tables

namespace OAI

section Inline_PCPProjectionProductTable
namespace MetricKMedian.PCP.Compiler.ProjectionTable
open Binary Binary.Automatic
open scoped Classical

variable {A B A' B' : Type} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Inhabited B] [Inhabited B']
noncomputable def combine (n : ℕ) (e : ProjectionRow A B) (f : ProjectionRow A' B') :
    ProjectionRow (A×A') (B×B') := (f.1+n*e.1,fun a=>(e.2 a.1,f.2 a.2))
lemma poly_combine : Poly (fun z : (ℕ×ProjectionRow A B)×ProjectionRow A' B' =>combine z.1.1 z.1.2 z.2) := by
  have hh : Poly (fun p : (A→B)×(A'→B') =>fun a : A×A'=>(p.1 a.1,p.2 a.2)) := hardcoded _
  exact Poly.pair (by fun_prop) (hh.comp (Poly.pair (Poly.snd.comp (Poly.snd.comp Poly.fst)) (Poly.snd.comp Poly.snd)))
noncomputable def product (t : ProjectionTable A B) (u : ProjectionTable A' B') : ProjectionTable (A×A') (B×B') :=
  (t.1.flatMap (fun _=>u.1),t.2.flatMap (fun row => u.2.map (fun row' => row.flatMap (fun e => row'.map (combine u.1.length e)))))
lemma poly_product : Poly (fun p : ProjectionTable A B×ProjectionTable A' B' =>product p.1 p.2) := by
  unfold product
  apply Poly.pair
  · exact Poly.list_flatMap (by fun_prop) (by fun_prop)
  · apply Poly.list_flatMap _ (by fun_prop)
    apply Poly.list_map _ (by fun_prop)
    apply Poly.list_flatMap _ (by fun_prop)
    apply Poly.list_map _ (by fun_prop)
    exact poly_combine.comp (Poly.pair (Poly.pair (by fun_prop) (Poly.snd.comp (Poly.fst))) Poly.snd)
variable {U V D S U' V' D' S' : Type}
  [Fintype U] [Fintype V] [Fintype D] [Fintype S]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S']
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
  [DecidableEq V'] [DecidableEq S'] [DecidableEq A'] [DecidableEq B']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')
  {n n' : ℕ} (ue : U≃Fin n) (ue' : U'≃Fin n')
  (vo : Ordered V) (vo' : Ordered V') (so : Ordered S) (so' : Ordered S')
omit [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Inhabited B] [Inhabited B']
  [Fintype U] [Fintype V] [Fintype D] [Fintype S]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S']
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
  [DecidableEq V'] [DecidableEq S'] [DecidableEq A'] [DecidableEq B'] in
lemma product_build : product (build G ue vo so) (build H ue' vo' so')=
    build (G.prod H) ((ue.prodCongr ue').trans finProdFinEquiv) (vo.prod vo') (so.prod so') := by
  apply Prod.ext
  · apply unitList_eq_length
    simp only [product,build,List.length_replicate]
    rw [length_flatMap_uniform _ _ n' (by intros; simp only [List.length_replicate])]
    simp only [List.length_replicate]
  · simp only [product,build,Ordered.prod,List.product,List.flatMap_map,List.map_flatMap,List.map_map,
      Function.comp_def,combine,List.length_replicate,BiProjection.prod,Equiv.trans_apply,
      Equiv.prodCongr_apply,Prod.map,finProdFinEquiv]
    rfl
end MetricKMedian.PCP.Compiler.ProjectionTable

end Inline_PCPProjectionProductTable

end OAI
