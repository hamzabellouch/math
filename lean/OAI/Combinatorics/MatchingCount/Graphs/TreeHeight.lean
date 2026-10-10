import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeBagBuild

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

lemma logicalB_nonneg {n : ℕ} (w : Fin n→Fin n→ℚ) (a b : Fin n) :
    0≤RationalSource.logicalB w a b :=
  (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ a b)
lemma sourceHeight_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (a : Fin n) : 0≤RationalSource.height w a := by
  obtain ⟨b,hb⟩:=Counting.others_nonempty hn a
  exact (logicalB_nonneg w a b).trans (Finset.le_sup' _ hb)
lemma sourceMaxHeight_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) : 0≤RationalSource.maxHeight w := by
  exact (sourceHeight_nonneg hn w ⟨0,by omega⟩).trans (Finset.le_sup' _ (Finset.mem_univ _))

lemma maxHeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    maxHeight (close (matrixRep w))=TreeFraction.repr (RationalSource.maxHeight w) := by
  rw [close_matrixRep w hw]
  have hc : BottleneckAlgorithm.close w n=RationalSource.logicalB w := by
    simp only [RationalSource.logicalB,Fintype.card_fin]
  rw [hc]
  unfold maxHeight
  have he : (List.range (matrixRep (RationalSource.logicalB w)).length).map
      (fun i=>height (matrixRep (RationalSource.logicalB w),i))=
      (List.ofFn (RationalSource.height w)).map TreeFraction.repr := by
    rw [matrixRep_length,ExecutableDP.map_range_ofFn,List.map_ofFn]
    congr 1
    funext i
    exact height_rep hn _ (logicalB_nonneg w) i
  rw [he]
  change ((List.ofFn (RationalSource.height w)).map TreeFraction.repr).foldl _ (TreeFraction.repr 0)=_
  rw [maximum_fold_repr _ 0 le_rfl (by
    intro x hx
    obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hx
    exact sourceHeight_nonneg hn w a)]
  rw [fold_max_ofFn _ 0 ⟨0,by omega⟩]
  congr 1
  exact max_eq_right (sourceMaxHeight_nonneg hn w)

def hierarchyFuel (x : Matrix×List Bool) : List Bool :=
  x.2.take (ExecutableHierarchy.level (x.2.length,maxHeight (close x.1)))
def hierarchyFuelRealizer : Realizer hierarchyFuel := (composition
  (pair second (composition (pair (composition second listLength)
    (composition (composition first closeRealizer) maxHeightRealizer)) levelRealizer)) takeFast).congr (fun _=>rfl)
lemma polynomial_hierarchyFuel : PolynomialTime hierarchyFuelRealizer := by
  unfold hierarchyFuelRealizer
  apply polynomial_congr
  have := polynomial_close
  have := polynomial_maxHeight
  have := polynomial_level
  have := polynomial_takeFast (A:=Bool)
  tree_cost
lemma hierarchyFuel_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    hierarchyFuel (matrixRep w,List.replicate (2*K) false)=
      List.replicate (RationalSource.levels w K) false := by
  unfold hierarchyFuel
  dsimp only
  rw [maxHeight_source hn w hw,List.length_replicate,level_repr _ _ (sourceMaxHeight_nonneg hn w)]
  rw [List.take_replicate]
  congr 1
  exact min_eq_left (Nat.findGreatest_le _)

def setupBags (x : BagBuildInput) : ExecutableDP.Bags :=
  buildBags (x.1,hierarchyFuel (x.1.1.1,x.2))
def setupBagsRealizer : Realizer setupBags := (composition
  (pair first (composition (pair first.fst.fst second) hierarchyFuelRealizer)) buildBagsRealizer).congr (fun _=>rfl)
lemma polynomial_setupBags : PolynomialTime setupBagsRealizer := by
  unfold setupBagsRealizer
  apply polynomial_congr
  have := polynomial_hierarchyFuel
  have := polynomial_buildBags
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

attribute [local instance] NumberedHierarchy.labelOrder
lemma setupBags_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    List.Forall₂ List.Perm
      (setupBags (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  unfold setupBags
  dsimp only
  rw [hierarchyFuel_source hn w hw K]
  exact buildBags_source hn w hw K

theorem setupBags_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine setupBagsRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine setupBagsRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (setupBags x)) :=
  TreePost.polynomial_compiles setupBagsRealizer polynomial_setupBags
end MatchingFPRAS.ExecutableSource

end OAI
