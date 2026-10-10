import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeScanRun
import OAI.Combinatorics.MatchingCount.Machines.TreeRefreshIndexed
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization
import OAI.Combinatorics.MatchingCount.Sampling.TreeIndexedPair

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder

abbrev PairSetup := (List (ℕ×ℕ)×List (List Fraction))×(Finset ℕ×Finset ℕ)
abbrev RefreshSetup := List ExecutableRefresh.Key×ExecutableDP.CountInput
abbrev Context := (PairSetup×RefreshSetup)×List (List ℕ)
abbrev Bits := List Bool×ExecutableUnit.Bits

def row (x : Context×ℕ) : List Fraction := x.1.1.1.1.2.getD x.2 []
def rowRealizer : Realizer row := composition (pair first.fst.fst.fst.snd second) (getDFast [])
lemma polynomial_row : PolynomialTime rowRealizer := by
  unfold rowRealizer row Realizer.fst Realizer.snd
  have := polynomial_getDFast ([] : List Fraction)
  tree_cost

def guide (x : Context×(ℕ×ℕ)) : Bool := decide (x.2.2∈x.1.2.getD x.2.1 [])
def guideRealizer : Realizer guide := composition
  (pair (composition (pair first.snd second.fst) (getDFast [])) second.snd) membership
lemma polynomial_guide : PolynomialTime guideRealizer := by
  unfold guideRealizer guide Realizer.fst Realizer.snd
  have := polynomial_membership
  have := polynomial_getDFast ([] : List ℕ)
  tree_cost

def pairContext (x : Context×(ℕ×ℕ)) : ExecutablePair.Context :=
  (x.1.1.1.1.1,(row (x.1,x.2.1),row (x.1,x.2.2)))
def pairContextRealizer : Realizer pairContext := pair first.fst.fst.fst.fst
  (pair (composition (pair first second.fst) rowRealizer) (composition (pair first second.snd) rowRealizer))
lemma polynomial_pairContext : PolynomialTime pairContextRealizer := by
  unfold pairContextRealizer pairContext Realizer.fst Realizer.snd
  have := polynomial_row
  tree_cost

def pairDraw (x : LocalPairInput Context ℕ (Finset ℕ) Bits) : Finset ℕ×Finset ℕ :=
  ExecutablePair.draw ((((pairContext x.1,x.1.1.1.1.2),x.2.1)),x.2.2.1)
def pairRealizer : Realizer pairDraw := (composition
  (pair (pair (pair (composition first pairContextRealizer) first.fst.fst.fst.snd) second.fst)
    second.snd.fst) ExecutablePair.drawRealizer).congr (fun _=>rfl)
lemma polynomial_pair : PolynomialTime pairRealizer := by
  unfold pairRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_pairContext
  have := ExecutablePair.polynomial_draw
  tree_cost

def refresh (x : LocalRefreshInput Context ℕ Bits) : Finset ℕ :=
  ExecutableRefresh.refresh (x.1.1.1.2,x.2.2)
def refreshRealizer : Realizer refresh := composition
  (pair first.fst.fst.snd second.snd) ExecutableRefresh.refreshRealizer
lemma polynomial_refresh : PolynomialTime refreshRealizer := by
  unfold refreshRealizer refresh Realizer.fst Realizer.snd
  have := ExecutableRefresh.polynomial_refresh
  tree_cost

abbrev Input := List (List Bool×Bits)×(RunSetup Context ℕ ℕ×StateTable ℕ (Finset ℕ))
def execute (x : Input) : RunSetup Context ℕ ℕ×StateTable ℕ (Finset ℕ) :=
  x.1.foldl (fun z b=>runStep guide pairDraw refresh (b,z)) x.2
def executeRealizer : Realizer execute :=
  fold (runStepRealizer guideRealizer pairRealizer refreshRealizer natEqual leNat natEqual)
lemma polynomial_execute : PolynomialTime executeRealizer :=
  polynomial_scanRun polynomial_guide polynomial_pair polynomial_refresh polynomial_natEqual
    polynomial_leNat polynomial_natEqual

theorem execute_post : ∃ p : Polynomial ℕ,∀ x : Input,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine executeRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine executeRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (execute x)) :=
  TreePost.polynomial_compiles executeRealizer polynomial_execute
end MatchingFPRAS.NumericLadder

end OAI
