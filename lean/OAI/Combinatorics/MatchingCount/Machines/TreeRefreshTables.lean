import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeInitialMatching
import OAI.Combinatorics.MatchingCount.Machines.TreeOrderedTransport
import OAI.Combinatorics.MatchingCount.Graphs.TreeBags

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableRefresh NumberedHierarchy

def labelIndices (x : HierarchyInput) : List ℕ := List.range (labels x).length
def labelIndicesRealizer : Realizer labelIndices := (composition
  labelsRealizer (composition listLength range)).congr (fun _=>rfl)
lemma polynomial_labelIndices : PolynomialTime labelIndicesRealizer := by
  unfold labelIndicesRealizer
  apply polynomial_congr
  have h : PolynomialTime (composition (listLength (A:=LabelKey)) range) :=
    polynomial_boundedRange polynomial_listLength Polynomial.X (fun x=>by
      simpa using list_length_le_weight x)
  exact polynomial_composition polynomial_labels h

def refreshTables (x : BagInput) : InitialInput :=
  let a:=bagTable x
  (storedCatalog (a,labelIndices x.1),((a,parents x.1),rankPlan (ranks x.1)))
def refreshTablesRealizer : Realizer refreshTables := (pair
  (composition (pair bagTableRealizer (composition first labelIndicesRealizer)) storedCatalogRealizer)
  (pair (pair bagTableRealizer (composition first parentsRealizer))
    (composition (composition first ranksRealizer) rankPlanRealizer))).congr (fun _=>rfl)
lemma polynomial_refreshTables : PolynomialTime refreshTablesRealizer := by
  unfold refreshTablesRealizer
  apply polynomial_congr
  have := polynomial_bagTable
  have := polynomial_labelIndices
  have := polynomial_storedCatalog
  have := polynomial_parents
  have := polynomial_ranks
  have := polynomial_rankPlan
  tree_cost

def initialFromHierarchy (x : BagInput) : Finset ℕ := ExecutableRefresh.initial (refreshTables x)
def initialFromHierarchyRealizer : Realizer initialFromHierarchy := composition refreshTablesRealizer initialRealizer
lemma polynomial_initialFromHierarchy : PolynomialTime initialFromHierarchyRealizer :=
  polynomial_composition polynomial_refreshTables polynomial_initial

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
include hB in
lemma arbitrary_labelIndices (xs : List Bool) :
    labelIndices (ExecutableBottleneck.matrixRep (reindex B (orderedIso V)),xs)=
      List.range (Fintype.card (Label B xs.length)) := by
  unfold labelIndices
  rw [labels_eq_ofFn _ (fun i j=>hB _ _),List.length_ofFn,
    Fintype.card_congr (labelReindex B (orderedIso V) xs.length)]

variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,(index (left e),index (right e))=p)

include hB in
lemma refreshTables_rep :
    refreshTables ((ExecutableBottleneck.matrixRep (reindex B (orderedIso V)),xs),es)=
    let a:=bagTable ((ExecutableBottleneck.matrixRep (reindex B (orderedIso V)),xs),es)
    (storedCatalog (a,List.range (Fintype.card (Label B xs.length))),
      ((a,parentRep (UnitRefresh.numberedParent (parent B hsym htri (H:=xs.length)))),
        (UnitRefresh.Materialized.plan (UnitRefresh.numberedRank
          (fun l : Label B xs.length=>l.1.val))).map Fin.val)) := by
  unfold refreshTables
  dsimp only
  rw [arbitrary_labelIndices B hB,arbitrary_parents B hB hsym htri,arbitrary_plan B hB]

include hB hes in
lemma initialFromHierarchy_valid
    (hb : UnitRefresh.RankedBags (bags B hsym htri left right xs.length)
      (fun l=>l.1.val) (parent B hsym htri))
    (hne : ∀ v,(bags B hsym htri left right xs.length v).Nonempty)
    (hex : Nonempty (Transport.BagPM (bags B hsym htri left right xs.length))) :
    ∃ M : Transport.BagPM (bags B hsym htri left right xs.length),
      initialFromHierarchy ((ExecutableBottleneck.matrixRep (reindex B (orderedIso V)),xs),es)=
        Numbered.set M.val := by
  unfold initialFromHierarchy
  rw [refreshTables_rep B hB hsym htri]
  exact initial_valid _ _ _ hb hne (fun l p h=>parent_rank B hsym htri h) hex _
    (arbitrary_bagTable_numbered B hB hsym htri xs left right es hes xs.length rfl)

include hB hes in
lemma initialFromHierarchy_valid_fintype (H : ℕ) (hH : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    UnitRefresh.RankedBags (bags B hsym htri left right H)
      (fun l=>l.1.val) (parent B hsym htri) →
    (∀ v,(bags B hsym htri left right H v).Nonempty) →
    Nonempty (Transport.BagPM (bags B hsym htri left right H)) →
    ∃ M : Transport.BagPM (bags B hsym htri left right H),
      initialFromHierarchy ((ExecutableBottleneck.matrixRep (fun i j=> B
        (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es)=
        Numbered.set M.val := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact initialFromHierarchy_valid B hB hsym htri xs left right es hes

open TreePost Turing

theorem initialFromHierarchy_post : ∃ p : Polynomial ℕ,∀ x : BagInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine initialFromHierarchyRealizer.program) (packed x) coins).state=none ∧
      (run (machine initialFromHierarchyRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (initialFromHierarchy x)) :=
  polynomial_compiles initialFromHierarchyRealizer polynomial_initialFromHierarchy
end MatchingFPRAS.ExecutableHierarchy

end OAI
