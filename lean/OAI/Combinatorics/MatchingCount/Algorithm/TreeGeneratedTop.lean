import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedPrepared
import OAI.Combinatorics.MatchingCount.Machines.TreeStart
import OAI.Combinatorics.MatchingCount.Sampling.TreePreparedTop

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev GeneratedTopInput := List (List Bool×Bits)×GeneratedInput
def generatedTop (x : GeneratedTopInput) : Finset ℕ :=
  preparedTop (x.1,(generatedPrepared x.2,exactStart x.2.1.1))
def generatedTopRealizer : Realizer generatedTop := (composition
  (pair first (pair (composition second generatedPreparedRealizer)
    (composition second.fst.fst exactStartRealizer))) preparedTopRealizer).congr (fun _=>rfl)
lemma polynomial_generatedTop : PolynomialTime generatedTopRealizer := by
  unfold generatedTopRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_generatedPrepared
  have := polynomial_exactStart
  have := polynomial_preparedTop
  tree_cost

lemma bagWeight_nonneg {n : ℕ} [Nontrivial (Fin n)]
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ)
    (e : BagEdge (RationalSource.bags w K)) : 0≤RationalSource.bagWeight w K D e :=
  add_nonneg (RationalSource.realPortion_nonneg w hw K e)
    (div_nonneg (by unfold RationalSource.bagHeight; positivity) (Nat.cast_nonneg D))

lemma generatedTop_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k) :
    generatedTop (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)))=
      Numbered.set (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
        (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
        (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
        (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
        (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val := by
  unfold generatedTop
  dsimp only
  rw [generatedPrepared_source hn w (fun a b=>(hw a b).le) K D ft fq,
    exactStart_source hn he w (fun a b=>(hw a b).le) K]
  exact preparedTop_source (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
    (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
    (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
    (RationalSource.parent_rank w K) ft fq hq (RationalSource.bagWeight w K D)
    (bagWeight_nonneg w hw K D) (RationalSource.startMatching w K he) _
    (setupBags_source hn w (fun a b=>(hw a b).le) K) bits

open TreePost Turing

theorem generatedTop_post : ∃ p : Polynomial ℕ,∀ x : GeneratedTopInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine generatedTopRealizer.program) (packed x) coins).state=none ∧
      (run (machine generatedTopRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (generatedTop x)) :=
  polynomial_compiles generatedTopRealizer polynomial_generatedTop
end MatchingFPRAS.ExecutableSource

end OAI
