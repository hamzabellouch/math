import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeWeightTable
import OAI.Combinatorics.MatchingCount.Machines.TreeMetadata
import OAI.Combinatorics.MatchingCount.Sampling.TreePrepared

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def rangeFromList {A : Type} (xs : List A) : Finset ℕ := (List.range xs.length).toFinset
def rangeFromListRealizer {A : Type} [Codec A] : Realizer (rangeFromList (A:=A)) :=
  composition (composition listLength range) (listFinset natEqual leNat)
lemma polynomial_rangeFromList {A : Type} [Codec A] : PolynomialTime (rangeFromListRealizer (A:=A)) := by
  apply polynomial_composition _ (polynomial_listFinset polynomial_natEqual polynomial_leNat)
  exact polynomial_boundedRange polynomial_listLength Polynomial.X (fun x=>by
    simpa using list_length_le_weight x)
lemma range_card_set (A : Type) [Fintype A] [LinearOrder A] :
    Finset.range (Fintype.card A)=Numbered.set (Finset.univ : Finset A) := by
  ext i
  simp only [Finset.mem_range,Numbered.set,Finset.mem_map,Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · intro h
    exact ⟨UnitRefresh.orderedEnum A ⟨i,h⟩,index_orderedEnum _⟩
  · rintro ⟨a,rfl⟩
    exact ((UnitRefresh.orderedEnum A).symm a).isLt

def sourceVertices (x : BagBuildInput) : List RawVertex := vertices (x.1.2,x.1.1.2)
def sourceVerticesRealizer : Realizer sourceVertices := composition
  (pair first.snd first.fst.snd) verticesRealizer
lemma polynomial_sourceVertices : PolynomialTime sourceVerticesRealizer :=
  polynomial_composition (polynomial_pair (polynomial_snd polynomial_first)
    (polynomial_snd (polynomial_fst polynomial_first))) polynomial_vertices
lemma sourceVertices_length {n : ℕ} (w : Fin n→Fin n→ℚ) (K : ℕ) :
    (sourceVertices (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)).length=
      Fintype.card (SourceVertex (Fin n) K) := by
  unfold sourceVertices
  dsimp only
  rw [vertices_eq_ofFn_length n _ (4*(2*K+2)) (by simp),List.length_ofFn]

def sourceEdgeData (x : BagBuildInput) : List (ℕ×ℕ)×(Finset ℕ×Finset ℕ) :=
  (((sourceTables x).1.map Prod.fst),(rangeFromList (sourceVertices x),rangeFromList (sourceTables x).1))
def sourceEdgeDataRealizer : Realizer sourceEdgeData := (pair
  (composition sourceTablesRealizer.fst (map first))
  (pair (composition sourceVerticesRealizer rangeFromListRealizer)
    (composition sourceTablesRealizer.fst rangeFromListRealizer))).congr (fun _=>rfl)
lemma polynomial_sourceEdgeData : PolynomialTime sourceEdgeDataRealizer := by
  unfold sourceEdgeDataRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sourceTables
  have := polynomial_sourceVertices
  have hrv := polynomial_rangeFromList (A:=RawVertex)
  have hrk := polynomial_rangeFromList (A:=Key)
  tree_cost
lemma sourceCatalog_endpoints {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
    (bags : V→Finset L) : (sourceCatalog bags).map Prod.fst=
      List.ofFn (fun e=>ExecutablePair.endpointRep (UnitRefresh.orderedEnum (Transport.BagEdge bags) e).val.val.1) := by
  unfold sourceCatalog
  rw [List.map_ofFn]
  rfl
lemma sourceEdgeData_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceEdgeData (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      (List.ofFn (fun e=>ExecutablePair.endpointRep
        (UnitRefresh.orderedEnum (Transport.BagEdge (RationalSource.bags w K)) e).val.val.1),
       (Numbered.set (Finset.univ : Finset (SourceVertex (Fin n) K)),
        Numbered.set (Finset.univ : Finset (Transport.BagEdge (RationalSource.bags w K))))) := by
  unfold sourceEdgeData
  rw [sourceTables_catalog hn w hw K,sourceCatalog_endpoints]
  apply Prod.ext
  · rfl
  unfold rangeFromList
  rw [sourceVertices_length,List.toFinset_range,range_card_set]
  unfold sourceCatalog
  rw [List.length_ofFn,List.toFinset_range,range_card_set]

abbrev GeneratedInput := (BagBuildInput×ℕ)×(List Bool×List Bool)
def generatedTier (x : GeneratedInput) : TierData :=
  (((sourceVertices x.1.1).length,x.2.1),(x.2.2,sourceWeights x.1))
def generatedTierRealizer : Realizer generatedTier := (pair
  (pair (composition (composition first.fst sourceVerticesRealizer) listLength) second.fst)
  (pair second.snd (composition first sourceWeightsRealizer))).congr (fun _=>rfl)
lemma polynomial_generatedTier : PolynomialTime generatedTierRealizer := by
  unfold generatedTierRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sourceVertices
  have := polynomial_sourceWeights
  tree_cost

def generatedPrepared (x : GeneratedInput) : Prepared :=
  ((generatedTier x,sourceEdgeData x.1.1),sourceTables x.1.1)
def generatedPreparedRealizer : Realizer generatedPrepared := (pair
  (pair generatedTierRealizer (composition first.fst sourceEdgeDataRealizer))
  (composition first.fst sourceTablesRealizer)).congr (fun _=>rfl)
lemma polynomial_generatedPrepared : PolynomialTime generatedPreparedRealizer := by
  unfold generatedPreparedRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_generatedTier
  have := polynomial_sourceEdgeData
  have := polynomial_sourceTables
  tree_cost

lemma generatedPrepared_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K D : ℕ) (ft fq : List Bool) :
    let x : BagBuildInput:=(((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)
    generatedPrepared ((x,D),(ft,fq))=
      sourcePrepared (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
        (RationalSource.bagWeight w K D) (setupBags x) ft fq := by
  dsimp only
  unfold generatedPrepared generatedTier
  dsimp only
  rw [sourceVertices_length,sourceWeights_source hn w hw K D,sourceEdgeData_source hn w hw K,
    sourceTables_source hn w hw K]
  unfold sourcePrepared
  rw [storedCatalog_source _ (setupBags_source hn w hw K)]

open TreePost Turing

theorem generatedPrepared_post : ∃ p : Polynomial ℕ,∀ x : GeneratedInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine generatedPreparedRealizer.program) (packed x) coins).state=none ∧
      (run (machine generatedPreparedRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (generatedPrepared x)) :=
  polynomial_compiles generatedPreparedRealizer polynomial_generatedPrepared
end MatchingFPRAS.ExecutableSource

end OAI
