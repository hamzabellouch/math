import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePortion

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
lemma arbitrary_ranks_fintype (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (xs : List Bool) (H : ℕ) (hH : xs.length=H) (F : Fintype (Label B H)) :
    letI := F
    ranks (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)=
      List.ofFn (UnitRefresh.numberedRank (fun a : Label B H=>a.1.val)) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_ranks B hB xs
end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceRanks (x : BagBuildInput) : List ℕ := ranks (setupHierarchy x).1
def sourceRanksRealizer : Realizer sourceRanks := composition setupHierarchyRealizer.fst ranksRealizer
lemma polynomial_sourceRanks : PolynomialTime sourceRanksRealizer :=
  polynomial_composition (polynomial_fst polynomial_setupHierarchy) polynomial_ranks
lemma sourceRanks_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceRanks (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      List.ofFn (UnitRefresh.numberedRank (fun a : RationalSource.Label w K=>a.1.val)) := by
  unfold sourceRanks setupHierarchy
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  exact arbitrary_ranks_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))

lemma rankLookup {L : Type} [Fintype L] [LinearOrder L] (rank : L→ℕ) (l : L) :
    (List.ofFn (UnitRefresh.numberedRank rank)).getD (index l) 0=rank l := by
  simp only [UnitRefresh.numberedRank,index,List.getD,List.getElem?_ofFn,
    ((UnitRefresh.orderedEnum L).symm l).isLt,↓reduceDIte,Fin.eta,Option.getD_some,Equiv.apply_symm_apply]

def sourceRank (x : BagBuildInput×Key) : ℕ := (sourceRanks x.1).getD x.2.2 0
def sourceRankRealizer : Realizer sourceRank := composition
  (pair (composition first sourceRanksRealizer) second.snd) (getDFast 0)
lemma polynomial_sourceRank : PolynomialTime sourceRankRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_sourceRanks)
    (polynomial_snd polynomial_second)) (polynomial_getDFast 0)
lemma sourceRank_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceRank ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),sourceKey e)=
      e.color.1.val := by
  unfold sourceRank
  dsimp only
  rw [sourceRanks_source hn w hw K]
  exact rankLookup _ _

def phantomHeight (x : BagBuildInput×Key) : Fraction := threshold (x.1.2,sourceRank x)
def phantomHeightRealizer : Realizer phantomHeight := composition
  (pair first.snd sourceRankRealizer) thresholdRealizer
lemma polynomial_phantomHeight : PolynomialTime phantomHeightRealizer :=
  polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) polynomial_sourceRank)
    polynomial_threshold
lemma phantomHeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    phantomHeight ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),sourceKey e)=
      TreeFraction.repr (RationalSource.bagHeight w K e.color) := by
  unfold phantomHeight
  dsimp only
  rw [sourceRank_source hn w hw K]
  apply threshold_repr
  rw [List.length_replicate]
  have h:=e.color.1.isLt
  have hh : RationalSource.levels w K≤2*K:=Nat.findGreatest_le _
  omega

def sourceBagWeight (x : (BagBuildInput×ℕ)×Key) : Fraction :=
  TreeFraction.add (realPart (x.1.1,x.2),
    TreeFraction.div (phantomHeight (x.1.1,x.2),(x.1.2,1)))
def sourceBagWeightRealizer : Realizer sourceBagWeight := (composition
  (pair (composition (pair first.fst second) realPartRealizer)
    (composition (pair (composition (pair first.fst second) phantomHeightRealizer)
      (pair first.snd (constant 1))) divRealizer)) addRealizer).congr (fun _=>rfl)
lemma polynomial_sourceBagWeight : PolynomialTime sourceBagWeightRealizer := by
  unfold sourceBagWeightRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_realPart
  have := polynomial_phantomHeight
  have := polynomial_div
  have := TreeFraction.polynomial_add
  tree_cost
lemma sourceBagWeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    sourceBagWeight (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      TreeFraction.repr (RationalSource.bagWeight w K D e) := by
  unfold sourceBagWeight
  dsimp only
  rw [realPart_source hn w hw K,phantomHeight_source hn w hw K]
  have hreal : 0≤RationalSource.realPortion w K e := by
    unfold RationalSource.realPortion
    apply Finset.sum_nonneg
    intro a _
    split_ifs <;> first | exact pathActivity_nonneg hn w hw K _ _ | exact le_rfl
  have hh : 0≤RationalSource.bagHeight w K e.color := by unfold RationalSource.bagHeight; positivity
  have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
  rw [hD,div_repr hh (Nat.cast_nonneg D),add_repr hreal (div_nonneg hh (Nat.cast_nonneg D))]
  rfl

open TreePost Turing

theorem sourceBagWeight_post : ∃ p : Polynomial ℕ,∀ x : (BagBuildInput×ℕ)×Key,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sourceBagWeightRealizer.program) (packed x) coins).state=none ∧
      (run (machine sourceBagWeightRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sourceBagWeight x)) :=
  polynomial_compiles sourceBagWeightRealizer polynomial_sourceBagWeight
end MatchingFPRAS.ExecutableSource

end OAI
