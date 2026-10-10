import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization
import OAI.Combinatorics.MatchingCount.Machines.TreeBuild
import OAI.Combinatorics.MatchingCount.Graphs.TreeBags

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
local instance : BEq RawVertex := ⟨fun a b=>decide (a=b)⟩
local instance : LawfulBEq RawVertex where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

def endpointEntry (x : (GeometryInput×List RawVertex)×RawReal) : ℕ×ℕ :=
  (x.1.2.idxOf (left (x.1.1,x.2)),x.1.2.idxOf (right (x.1.1,x.2)))
def endpointEntryRealizer : Realizer endpointEntry := (pair
  (composition (pair (composition (pair first.fst second) leftRealizer) first.snd) (indexOf vertexEqual))
  (composition (pair (composition (pair first.fst second) rightRealizer) first.snd) (indexOf vertexEqual))).congr (fun _=>rfl)
lemma polynomial_endpointEntry : PolynomialTime endpointEntryRealizer := by
  unfold endpointEntryRealizer
  apply polynomial_congr
  have := polynomial_indexOf polynomial_vertexEqual
  have := polynomial_left
  have := polynomial_right
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def endpointList (x : GeometryInput) : List (ℕ×ℕ) :=
  (realEdges x).map (fun e=>endpointEntry ((x,vertices x),e))
def endpointListRealizer : Realizer endpointList := composition
  (pair (pair identity verticesRealizer) realEdgesRealizer) (mapWith endpointEntryRealizer)
lemma polynomial_endpointList : PolynomialTime endpointListRealizer := by
  unfold endpointListRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_identity
    polynomial_vertices) polynomial_realEdges) (polynomial_mapWith polynomial_endpointEntry)

lemma index_vertices {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (v : SourceVertex (Fin n) K) : (vertices (List.range n,fuel)).idxOf (vertexRepr v)=index v := by
  rw [vertices_eq_ofFn_length n fuel _ (by rw [hf])]
  let e:=UnitRefresh.orderedEnum (SourceVertex (Fin n) K)
  let i:=e.symm v
  have hn : (List.ofFn (fun j=>vertexRepr (e j))).Nodup :=
    List.nodup_ofFn.mpr (vertexRepr_injective.comp e.injective)
  have hi : i.val<(List.ofFn (fun j=>vertexRepr (e j))).length := by simpa only [List.length_ofFn] using i.isLt
  have he:=@List.Nodup.idxOf_getElem RawVertex _ _ _ hn i.val hi
  simpa only [List.getElem_ofFn,Fin.eta,i,Equiv.apply_symm_apply,e,index] using he

lemma endpointEntry_source {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    endpointEntry (((List.range n,fuel),vertices (List.range n,fuel)),realRepr e)=
      (index (realLeft K e),index (realRight K e)) := by
  have h:=ends_source_repr K fuel hf e
  have hl:=congrArg Prod.fst h
  have hr:=congrArg Prod.snd h
  unfold endpointEntry
  dsimp only at hl hr ⊢
  rw [hl,hr,index_vertices K fuel hf,index_vertices K fuel hf]
  rfl

lemma endpointList_members {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (p : ℕ×ℕ) : p∈endpointList (List.range n,fuel) ↔
      ∃ e : SourceRealEdge (Fin n) K,(index (realLeft K e),index (realRight K e))=p := by
  have hm (e : RawReal) : e∈realEdges (List.range n,fuel) ↔
      ∃ a : SourceRealEdge (Fin n) K,realRepr a=e := by
    rw [←List.mem_toFinset,realEdges_finset n K fuel hf]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
  simp only [endpointList,List.mem_map,hm]
  constructor
  · rintro ⟨e,⟨a,rfl⟩,hp⟩
    exact ⟨a,(endpointEntry_source K fuel hf a).symm.trans hp⟩
  · rintro ⟨e,he⟩
    exact ⟨realRepr e,⟨e,rfl⟩,(endpointEntry_source K fuel hf e).trans he⟩

abbrev BagBuildInput := BuildInput×List Bool
def buildBags (x : BagBuildInput) : ExecutableDP.Bags :=
  bagTable ((buildClosure x.1,x.2),endpointList (x.1.2,x.1.1.2))
def buildBagsRealizer : Realizer buildBags := (composition
  (pair (pair (composition first buildClosureRealizer) second)
    (composition (pair first.snd first.fst.snd) endpointListRealizer)) bagTableRealizer).congr (fun _=>rfl)
lemma polynomial_buildBags : PolynomialTime buildBagsRealizer := by
  unfold buildBagsRealizer
  apply polynomial_congr
  have := polynomial_buildClosure
  have := polynomial_endpointList
  have := polynomial_bagTable
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

lemma source_bagTable {n : ℕ} [Nontrivial (Fin n)]
    (w : Fin n→Fin n→ℚ) (K : ℕ) :
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>RationalSource.realB w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)),
        List.replicate (RationalSource.levels w K) false),
        endpointList (List.range n,List.replicate (2*K+2) false)))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  exact arbitrary_bagTable_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (realLeft K) (realRight K)
    (endpointList (List.range n,List.replicate (2*K+2) false))
    (endpointList_members K _ (List.length_replicate ..))
    (RationalSource.levels w K) (List.length_replicate ..)
    (inferInstance : Fintype (RationalSource.Label w K))

lemma buildBags_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    List.Forall₂ List.Perm
      (buildBags (((matrixRep w,List.replicate (2*K+2) false),List.range n),
        List.replicate (RationalSource.levels w K) false))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  unfold buildBags
  rw [buildClosure_repr hn w hw K]
  exact source_bagTable w K

theorem buildBags_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine buildBagsRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine buildBagsRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (buildBags x)) :=
  TreePost.polynomial_compiles buildBagsRealizer polynomial_buildBags
end MatchingFPRAS.ExecutableSource

end OAI
