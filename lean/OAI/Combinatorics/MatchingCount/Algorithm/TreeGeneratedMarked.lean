import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedTop
import OAI.Combinatorics.MatchingCount.Machines.TreeMarkTable
import OAI.Combinatorics.MatchingCount.Sampling.TreePreparedMarked

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def generatedContext (x : GeneratedInput) : SampleContext :=
  ((generatedPrepared x,exactStart x.1.1),sourceMarks x.1)
def generatedContextRealizer : Realizer generatedContext := (pair
  (pair generatedPreparedRealizer (composition first.fst exactStartRealizer))
  (composition first sourceMarksRealizer)).congr (fun _=>rfl)
lemma polynomial_generatedContext : PolynomialTime generatedContextRealizer := by
  unfold generatedContextRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_generatedPrepared
  have := polynomial_exactStart
  have := polynomial_sourceMarks
  tree_cost

def generatedMarked (x : GeneratedInput×SampleBits) : ExecutableMarking.Marks ℕ :=
  NumericMarking.sample (generatedContext x.1,x.2)
def generatedMarkedRealizer : Realizer generatedMarked := (composition
  (pair (composition first generatedContextRealizer) second) sampleRealizer).congr (fun _=>rfl)
lemma polynomial_generatedMarked : PolynomialTime generatedMarkedRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_generatedContext) polynomial_second)
    polynomial_sample)

lemma generatedMarked_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    generatedMarked
      ((((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),
       (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
        (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
        (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
        (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
        (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
          (fun e=>(RationalSource.markingTable w hw K D hD e).draw km (mb e)) := by
  unfold generatedMarked generatedContext
  dsimp only
  rw [generatedPrepared_source hn w (fun a b=>(hw a b).le) K D ft fq,
    exactStart_source hn he w (fun a b=>(hw a b).le) K,
    sourceMarks_source hn w hw K D hD]
  exact sample_source (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
    (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
    (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
    (RationalSource.parent_rank w K) ft fq hq (RationalSource.bagWeight w K D)
    (bagWeight_nonneg w hw K D) (RationalSource.startMatching w K he) _
    (setupBags_source hn w (fun a b=>(hw a b).le) K) _ bits mb

open TreePost Turing

theorem generatedMarked_post : ∃ p : Polynomial ℕ,∀ x : GeneratedInput×SampleBits,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine generatedMarkedRealizer.program) (packed x) coins).state=none ∧
      (run (machine generatedMarkedRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (generatedMarked x)) :=
  polynomial_compiles generatedMarkedRealizer polynomial_generatedMarked
end MatchingFPRAS.ExecutableSource

end OAI
