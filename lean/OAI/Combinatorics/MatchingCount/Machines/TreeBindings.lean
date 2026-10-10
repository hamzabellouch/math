import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedStage
import OAI.Combinatorics.MatchingCount.Machines.TreeScaleStateUpdate

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder ExecutableLadder NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder

lemma logicalEdges_eq_ofFn (n : ℕ) : logicalEdges (List.range n)=
    (List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin n)))).map logicalRepr := by
  classical
  rw [UnitRefresh.ofFn_orderedEnum]
  have ha : (logicalEdges (List.range n)).Pairwise (· ≤ ·) :=
    (logicalEdges_pairwise n).imp (fun h=>le_of_lt h)
  have hb : (((Finset.univ : Finset (LogicalEdge (Fin n))).sort (· ≤ ·)).map logicalRepr).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(logicalRepr_le _ _).mpr h)
  have hn : (logicalEdges (List.range n)).Nodup := (logicalEdges_pairwise n).imp (fun h=>h.ne)
  have hm := (Finset.sort_nodup (Finset.univ : Finset (LogicalEdge (Fin n))) (· ≤ ·)).map logicalRepr_injective
  have hp : (logicalEdges (List.range n)).Perm
      (((Finset.univ : Finset (LogicalEdge (Fin n))).sort (· ≤ ·)).map logicalRepr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext e
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
    constructor
    · exact logicalEdges_complete e
    · rintro ⟨a,rfl⟩; exact logicalRepr_mem a
  exact hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂) ha hb

def centralIndexArg : Realizer (fun x : BagBuildInput×RawLogical=>(x.1,centralKey x)) :=
  (TreeTyped.pair (first (A:=BagBuildInput) (B:=RawLogical)) centralKeyRealizer).congr (fun _=>rfl)
lemma polynomial_centralIndexArg : PolynomialTime centralIndexArg :=
  polynomial_congr _ (TreeTyped.polynomial_pair polynomial_first polynomial_centralKey)
def centralIndex (x : BagBuildInput×RawLogical) : ℕ := tableIndex (x.1,centralKey x)
def centralIndexRealizer : Realizer centralIndex :=
  (composition (f:=fun x : BagBuildInput×RawLogical=>(x.1,centralKey x)) (g:=tableIndex)
    centralIndexArg tableIndexRealizer).congr (by intro x; simp only [Function.comp_apply,centralIndex])
lemma polynomial_centralIndex : PolynomialTime centralIndexRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_centralIndexArg polynomial_tableIndex)
def centralBinding (x : BagBuildInput×RawLogical) : RawLogical×ℕ :=
  (x.2,centralIndex x)
def centralBindingRealizer : Realizer centralBinding :=
  (TreeTyped.pair (second (A:=BagBuildInput) (B:=RawLogical)) centralIndexRealizer).congr (fun _=>rfl)
lemma polynomial_centralBinding : PolynomialTime centralBindingRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair polynomial_second polynomial_centralIndex)

def sourceBindings (x : BagBuildInput) : Bindings :=
  (logicalEdges x.1.2).map (fun e=>centralBinding (x,e))
def sourceBindingsRealizer : Realizer sourceBindings := (rowsWith centralBindingRealizer
  (composition (first (A:=BuildInput) (B:=List Bool)).snd logicalEdgesRealizer)).congr (fun _=>rfl)
lemma polynomial_sourceBindings : PolynomialTime sourceBindingsRealizer :=
  polynomial_congr _ (polynomial_rowsWith polynomial_centralBinding
    (polynomial_composition (polynomial_snd polynomial_first) polynomial_logicalEdges))

lemma sourceBindings_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    sourceBindings (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      (List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin n)))).map
        (fun e=>(logicalRepr e,index (RationalSource.centralEdge w K e))) := by
  unfold sourceBindings
  rw [logicalEdges_eq_ofFn,List.map_map]
  apply List.map_congr_left
  intro e _he
  dsimp only [Function.comp_def,centralBinding,centralIndex]
  rw [centralKey_source hn w hw K]
  unfold tableIndex
  dsimp only
  rw [sourceTables_catalog hn w hw K,sourceCatalog_index]

abbrev GeneratedUpdateConfig := (BagBuildInput×ℕ)×ExecutableScaling.Vector
def generatedUpdateConfig (x : GeneratedUpdateConfig) : UpdateConfig :=
  ((x.1.2,x.1.1.1.2),(sourceBindings x.1.1,x.2))
def generatedUpdateConfigRealizer : Realizer generatedUpdateConfig := (pair
  (pair first.snd first.fst.fst.snd)
  (pair (composition first.fst sourceBindingsRealizer) second)).congr (fun _=>rfl)
lemma polynomial_generatedUpdateConfig : PolynomialTime generatedUpdateConfigRealizer := by
  unfold generatedUpdateConfigRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sourceBindings
  tree_cost

lemma generatedUpdateConfig_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    {j : ℕ} (s : FiniteTrial.ScaleState G j) (K : ℕ) :
    generatedUpdateConfig (((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),
      List.replicate (2*K) false),FiniteTrial.sourceD (G:=G) K),ExecutableScaling.vectorRep s.scale)=
      sourceUpdateConfig s K := by
  unfold generatedUpdateConfig sourceUpdateConfig
  dsimp only
  rw [sourceBindings_source hn s.activity (fun i j=>(s.activity_pos i j).le) K]
end MatchingFPRAS.ExecutableSource

end OAI
