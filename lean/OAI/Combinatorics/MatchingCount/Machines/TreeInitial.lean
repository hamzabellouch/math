import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalStart
import OAI.Combinatorics.MatchingCount.Machines.TreeRefreshTables
import OAI.Combinatorics.MatchingCount.Graphs.TreeHeight

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

def setupHierarchy (x : BagBuildInput) : BagInput :=
  ((buildClosure x.1,hierarchyFuel (x.1.1.1,x.2)),endpointList (x.1.2,x.1.1.2))
def setupHierarchyRealizer : Realizer setupHierarchy := (pair
  (pair (composition first buildClosureRealizer)
    (composition (pair first.fst.fst second) hierarchyFuelRealizer))
  (composition (pair first.snd first.fst.snd) endpointListRealizer)).congr (fun _=>rfl)
lemma polynomial_setupHierarchy : PolynomialTime setupHierarchyRealizer := by
  unfold setupHierarchyRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_buildClosure
  have := polynomial_hierarchyFuel
  have := polynomial_endpointList
  tree_cost

def sourceTables (x : BagBuildInput) : ExecutableRefresh.InitialInput :=
  refreshTables (setupHierarchy x)
def sourceTablesRealizer : Realizer sourceTables := composition setupHierarchyRealizer refreshTablesRealizer
lemma polynomial_sourceTables : PolynomialTime sourceTablesRealizer :=
  polynomial_composition polynomial_setupHierarchy polynomial_refreshTables

def sourceInitial (x : BagBuildInput) : Finset ℕ :=
  ExecutableRefresh.initial (sourceTables x)
def sourceInitialRealizer : Realizer sourceInitial := composition sourceTablesRealizer ExecutableRefresh.initialRealizer
lemma polynomial_sourceInitial : PolynomialTime sourceInitialRealizer :=
  polynomial_composition polynomial_sourceTables ExecutableRefresh.polynomial_initial

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
lemma sourceInitial_valid {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (hcap : ∀ i j,i≠j → BottleneckAlgorithm.edge w i j≤(4:ℚ)^K)
    (hex : Nonempty (Transport.BagPM (RationalSource.bags w K))) :
    ∃ M : Transport.BagPM (RationalSource.bags w K),
    sourceInitial (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      Numbered.set M.val := by
  change ∃ M : Transport.BagPM (RationalSource.bags w K),
    initialFromHierarchy (setupHierarchy (((matrixRep w,List.replicate (2*K+2) false),List.range n),
      List.replicate (2*K) false))=Numbered.set M.val
  unfold setupHierarchy
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  exact initialFromHierarchy_valid_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (realLeft K) (realRight K)
    (endpointList (List.range n,List.replicate (2*K+2) false))
    (endpointList_members K _ (List.length_replicate ..))
    (RationalSource.levels w K) (List.length_replicate ..)
    (inferInstance : Fintype (RationalSource.Label w K))
    (RationalSource.bags_ranked w K hcap) (RationalSource.bags_nonempty w K) hex

lemma sourceInitial_even {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ)
    (hcap : ∀ i j,i≠j → BottleneckAlgorithm.edge w i j≤(4:ℚ)^K) :
    ∃ M : Transport.BagPM (RationalSource.bags w K),
    sourceInitial (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      Numbered.set M.val :=
  sourceInitial_valid hn w hw K hcap ⟨RationalSource.startMatching w K he⟩

open TreePost Turing

theorem sourceInitial_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sourceInitialRealizer.program) (packed x) coins).state=none ∧
      (run (machine sourceInitialRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sourceInitial x)) :=
  polynomial_compiles sourceInitialRealizer polynomial_sourceInitial
end MatchingFPRAS.ExecutableSource

end OAI
