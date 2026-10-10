import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeColoredIndex
import OAI.Combinatorics.MatchingCount.Machines.TreeInitial

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceTables_catalog {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    (sourceTables (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)).1=
      sourceCatalog (RationalSource.bags w K) := by
  rw [sourceTables,refreshTables,setupHierarchy,
    buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  dsimp only
  rw [arbitrary_labelIndices_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))]
  have catalog := storedCatalog_source (bags:=RationalSource.bags w K) _ (source_bagTable w K)
  exact catalog

def coloredKey (x : HierarchyInput×(ℕ×ℕ)) : Key :=
  ((min x.2.1 x.2.2,max x.2.1 x.2.2),edgeIndex ((x.1,labels x.1),x.2))
def coloredKeyRealizer : Realizer coloredKey := (pair
  (pair (composition second TreeTyped.minimum) (composition second TreeTyped.maximum))
  (composition (pair (pair first (composition first labelsRealizer)) second) edgeIndexRealizer)).congr (fun _=>rfl)
lemma polynomial_coloredKey : PolynomialTime coloredKeyRealizer := by
  unfold coloredKeyRealizer
  apply polynomial_congr
  have := polynomial_labels
  have := polynomial_edgeIndex
  have hmax : PolynomialTime TreeTyped.maximum := by
    unfold TreeTyped.maximum
    exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_second polynomial_first)
  have hmin := TreeTyped.polynomial_minimum
  tree_cost

def sourceRealKey (x : BagBuildInput×RawReal) : Key :=
  coloredKey ((setupHierarchy x.1).1,
    endpointEntry (((x.1.1.2,x.1.1.1.2),vertices (x.1.1.2,x.1.1.1.2)),x.2))
def sourceRealKeyRealizer : Realizer sourceRealKey := (composition
  (pair (composition first setupHierarchyRealizer).fst
    (composition (pair (pair (pair first.fst.snd first.fst.fst.snd)
      (composition (pair first.fst.snd first.fst.fst.snd) verticesRealizer)) second) endpointEntryRealizer)) coloredKeyRealizer).congr (fun _=>rfl)
lemma polynomial_sourceRealKey : PolynomialTime sourceRealKeyRealizer := by
  unfold sourceRealKeyRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_setupHierarchy
  have := polynomial_vertices
  have := polynomial_endpointEntry
  have := polynomial_coloredKey
  tree_cost

lemma sourceRealKey_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : SourceRealEdge (Fin n) K) :
    sourceRealKey ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),realRepr e)=
      sourceKey (RationalSource.coloredReal w K e) := by
  unfold sourceRealKey setupHierarchy coloredKey
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K,
    endpointEntry_source K _ (List.length_replicate ..) e]
  dsimp only
  rw [arbitrary_edgeIndex_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (realLeft K) (realRight K)
    (RationalSource.levels w K) (List.length_replicate ..)
    (inferInstance : Fintype (RationalSource.Label w K)) e]
  exact (sourceKey_mk (RationalSource.coloredReal w K e) (realLeft K e) (realRight K e)
    (RationalSource.realLabel w K e) rfl).symm

def sourceRealIndex (x : BagBuildInput×RawReal) : ℕ :=
  (sourceTables x.1).1.idxOf (sourceRealKey x)
def keyLookup {A : Type} [Codec A] {f : A→Key} {g : A→List Key}
    (F : Realizer f) (G : Realizer g) : Realizer (fun x=>(g x).idxOf (f x)) :=
  composition (pair F G) (indexOf (pairEqual (pairEqual natEqual natEqual) natEqual))
lemma polynomial_keyLookup {A : Type} [Codec A] {f : A→Key} {g : A→List Key}
    {F : Realizer f} {G : Realizer g} (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (keyLookup F G) :=
  polynomial_composition (polynomial_pair hF hG)
    (polynomial_indexOf (polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual))
def sourceRealIndexRealizer : Realizer sourceRealIndex :=
  keyLookup sourceRealKeyRealizer (composition (first (A:=BagBuildInput) (B:=RawReal)) sourceTablesRealizer).fst
lemma polynomial_sourceRealIndex : PolynomialTime sourceRealIndexRealizer :=
  polynomial_keyLookup polynomial_sourceRealKey
    (polynomial_fst (polynomial_composition polynomial_first polynomial_sourceTables))
lemma sourceRealIndex_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (e : SourceRealEdge (Fin n) K) :
    sourceRealIndex ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),realRepr e)=
      index (RationalSource.coloredReal w K e) := by
  unfold sourceRealIndex
  rw [sourceTables_catalog hn w hw K,sourceRealKey_source hn w hw K,sourceCatalog_index]

open TreePost Turing

theorem sourceRealIndex_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput×RawReal,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sourceRealIndexRealizer.program) (packed x) coins).state=none ∧
      (run (machine sourceRealIndexRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sourceRealIndex x)) :=
  polynomial_compiles sourceRealIndexRealizer polynomial_sourceRealIndex

end MatchingFPRAS.ExecutableSource

end OAI
