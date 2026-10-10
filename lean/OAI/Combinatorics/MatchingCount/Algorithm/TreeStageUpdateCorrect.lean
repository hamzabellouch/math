import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericStage
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericSummaries

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
lemma finishUpdate_rep {E : Type} [Fintype E] [LinearOrder E] {n : ℕ} (hn : 2≤n)
    (c : Enlargement.LogicalEdge (Fin n)→E) (keys : List E) (hk : ∀ e,e∈keys)
    (z : E→ℚ) (hz : ∀ e,0≤z e) (D : ℕ) (d q : ℚ) (hd : 0≤d)
    (a : Fin n→ℚ) (ha : ∀ i,0≤a i) :
    finishUpdate (((D,List.range n),
        ((List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
          (fun e=>(logicalRepr e,index (c e))),vectorRep a)),
      ((TreeFraction.repr q,TreeFraction.repr d),keys.map (fun e=>(index e,TreeFraction.repr (z e)))))=
      (TreeFraction.repr q,vectorRep (fun i=>a i*
        Counting.scalingTrace hn (FiniteTrial.estimateMatrix D d (z ∘ c)) n i)) := by
  unfold finishUpdate
  dsimp only
  rw [logicalProbes_rep c keys hk z]
  have ht (e : Enlargement.LogicalEdge (Fin n)) :
      lookup (0,1) ((List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
        (fun e=>(logicalRepr e,TreeFraction.repr (z (c e)))),logicalRepr e)=
          TreeFraction.repr ((z ∘ c) e) := by
    apply lookup_image (0,1) _ logicalRepr (fun e=>TreeFraction.repr (z (c e))) logicalRepr_injective
    exact List.mem_ofFn.mpr ⟨(UnitRefresh.orderedEnum _).symm e,Equiv.apply_symm_apply _ _⟩
  rw [estimateMatrix_rep D d hd (z ∘ c) (fun e=>hz (c e)) _ ht,
    updateVector_rep hn _ (FiniteTrial.estimateMatrix_symm D d (z ∘ c))
      (fun i j _=>FiniteTrial.estimateMatrix_bounds D d (z ∘ c) i j) a ha]

abbrev AdaptiveInput := UpdateConfig×StageInput
def stageUpdate (x : AdaptiveInput) : Fraction×Vector :=
  finishUpdate (x.1,summaries (x.2.1.1,sampleMany (x.2.1.2,x.2.2)))
def stageUpdateRealizer : Realizer stageUpdate := (composition
  (pair first (composition (pair second.fst.fst
    (composition (pair second.fst.snd second.snd) sampleManyRealizer)) summariesRealizer)) finishUpdateRealizer).congr (fun _=>rfl)
lemma polynomial_stageUpdate : PolynomialTime stageUpdateRealizer := by
  unfold stageUpdateRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_sampleMany
  have := polynomial_summaries
  have := polynomial_finishUpdate
  tree_cost

theorem stageUpdate_post : ∃ p : Polynomial ℕ,∀ x : AdaptiveInput,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine stageUpdateRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine stageUpdateRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (stageUpdate x)) :=
  TreePost.polynomial_compiles stageUpdateRealizer polynomial_stageUpdate
end MatchingFPRAS.NumericMarking

end OAI
