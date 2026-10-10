import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeNumericLadder
import OAI.Combinatorics.MatchingCount.Machines.TreeGuideTables

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

abbrev Prepared := (TierData×(List (ℕ×ℕ)×(Finset ℕ×Finset ℕ)))×RefreshSetup

def prepareContext (x : Prepared) : Context :=
  ((((x.1.2.1,weightRows x.1.1),x.1.2.2),x.2),guideRows x.1.1)
def prepareContextRealizer : Realizer prepareContext := (pair
  (pair (pair (pair first.snd.fst (composition first.fst weightRowsRealizer)) first.snd.snd) second)
  (composition first.fst guideRowsRealizer)).congr (fun _=>rfl)
lemma polynomial_prepareContext : PolynomialTime prepareContextRealizer := by
  unfold prepareContextRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_weightRows
  have := polynomial_guideRows
  tree_cost

def baseTest (x : TierData×ℕ) : Bool := decide (x.2/x.1.2.1.length=x.1.1.2.length)
def baseTestRealizer : Realizer baseTest := (composition
  (pair (composition (pair second (composition first.snd.fst listLength)) quotient)
    (composition first.fst.snd listLength)) natEqual).congr (fun _=>rfl)
lemma polynomial_baseTest : PolynomialTime baseTestRealizer := by
  unfold baseTestRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_quotient
  tree_cost

def baseSet (x : TierData) : Finset ℕ := (slotUniverse x).filter fun i=>baseTest (x,i)
def baseSetRealizer : Realizer baseSet := composition (pair identity slotUniverseRealizer)
  (finsetFilterWith baseTestRealizer)
lemma polynomial_baseSet : PolynomialTime baseSetRealizer := by
  unfold baseSetRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity polynomial_slotUniverse)
    (polynomial_finsetFilterWith polynomial_baseTest)
lemma baseSet_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    baseSet ((n,ft),(fq,ws))=Numbered.set (base ft.length fq.length) := by
  rw [baseSet,slotUniverse_source]
  ext j
  simp only [Finset.mem_filter,Numbered.set,Finset.mem_map,Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · rintro ⟨⟨z,rfl⟩,h⟩
    refine ⟨z,?_,rfl⟩
    rw [mem_base]
    simpa [baseTest,slot_index_div] using h
  · rintro ⟨z,h,rfl⟩
    refine ⟨⟨z,rfl⟩,?_⟩
    simpa [baseTest,slot_index_div] using (mem_base z).mp h

def prepareSetup (x : Prepared) : RunSetup Context ℕ ℕ :=
  ((prepareContext x,(slotUniverse x.1.1,baseSet x.1.1)),(slots x.1.1,x.1.2.2.2))
def prepareSetupRealizer : Realizer prepareSetup := (pair
  (pair prepareContextRealizer (pair (composition first.fst slotUniverseRealizer)
    (composition first.fst baseSetRealizer)))
  (pair (composition first.fst slotsRealizer) first.snd.snd.snd)).congr (fun _=>rfl)
lemma polynomial_prepareSetup : PolynomialTime prepareSetupRealizer := by
  unfold prepareSetupRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_prepareContext
  have := polynomial_slotUniverse
  have := polynomial_baseSet
  have := polynomial_slots
  tree_cost

def prepareState (x : Prepared×Finset ℕ) : RunState Context ℕ ℕ :=
  (prepareSetup x.1,(slots x.1.1.1).map (fun i=>(i,x.2)))
def prepareStateRealizer : Realizer prepareState := (pair (composition first prepareSetupRealizer)
  (composition (pair second (composition first.fst.fst slotsRealizer)) (mapWith (pair second first)))).congr (fun _=>rfl)
lemma polynomial_prepareState : PolynomialTime prepareStateRealizer := by
  unfold prepareStateRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_prepareSetup
  have := polynomial_slots
  tree_cost

abbrev PreparedInput := List (List Bool×Bits)×(Prepared×Finset ℕ)
def preparedRun (x : PreparedInput) : RunState Context ℕ ℕ := execute (x.1,prepareState x.2)
def preparedRunRealizer : Realizer preparedRun := composition (pair first (composition second prepareStateRealizer)) executeRealizer
lemma polynomial_preparedRun : PolynomialTime preparedRunRealizer := by
  unfold preparedRunRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_prepareState)) polynomial_execute

def preparedTop (x : PreparedInput) : Finset ℕ := lookup ∅ ((preparedRun x).2,0)
def preparedTopRealizer : Realizer preparedTop := (composition
  (pair (composition (composition preparedRunRealizer second) identity) (constant 0)) (lookupRealizer ∅ natEqual)).congr (fun _=>rfl)
lemma polynomial_preparedTop : PolynomialTime preparedTopRealizer := by
  unfold preparedTopRealizer
  apply polynomial_congr
  have := polynomial_preparedRun
  have := polynomial_lookup (∅ : Finset ℕ) polynomial_natEqual
  tree_cost

theorem preparedTop_post : ∃ p : Polynomial ℕ,∀ x : PreparedInput,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine preparedTopRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine preparedTopRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (preparedTop x)) :=
  TreePost.polynomial_compiles preparedTopRealizer polynomial_preparedTop
end MatchingFPRAS.NumericLadder

end OAI
