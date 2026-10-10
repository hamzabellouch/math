import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastSample

namespace OAI

namespace MatchingFPRAS.ExecutableDP
lemma context_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (l : ℕ) (t : Table) :
    context ((a,ps),(l,t))=context ((b,ps),(l,t)) := by
  simp only [context,privateNumber_rows h,sharedNumber_rows h,totalNumber_rows h]
lemma cappedUpdate_rows {a b as bs : Bags} (h : List.Forall₂ List.Perm a b)
    (ho : List.Forall₂ List.Perm as bs) (ps : Parents) (ls : List ℕ) (l r : ℕ) (t : Table) :
    cappedUpdate ((((as,ps),ls),((a,ps),(l,t))),r)=
      cappedUpdate ((((bs,ps),ls),((b,ps),(l,t))),r) := by
  simp only [cappedUpdate,tabulate,cappedEntry,capBits,BInitial,nVertices,nLabels,nPlan,
    updateRows,updateColumns,rawEntry,context_rows h,ho.length_eq]
lemma runCapped_rows {a b as bs : Bags} (h : List.Forall₂ List.Perm a b)
    (ho : List.Forall₂ List.Perm as bs) (ps : Parents) (ls ks : List ℕ) (t : Table) :
    (runCapped ((as,ps),ls) ks a t).2=(runCapped ((bs,ps),ls) ks b t).2 := by
  induction ks generalizing a b t with
  | nil=>rfl
  | cons k ks ih=>
    simp only [runCapped,cappedUpdate_rows h ho]
    exact ih (trim_rows h k) _
lemma cappedCount_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) :
    cappedCount ((a,ps),ls)=cappedCount ((b,ps),ls) := by
  rw [cappedCount_run,cappedCount_run]
  simp only [nLabels,BInitial,nVertices,h.length_eq,runCapped_rows h h]
lemma rows_getD {a b : Bags} (h : List.Forall₂ List.Perm a b) (i : ℕ) :
    (a.getD i []).Perm (b.getD i []) := by
  induction h generalizing i with
  | nil=>exact List.Perm.refl []
  | @cons a b as bs hab _hs ih=>
    cases i with
    | zero=>exact hab
    | succ i=>exact ih i
end MatchingFPRAS.ExecutableDP

namespace MatchingFPRAS.ExecutableUnit
open ExecutableDP

lemma residual_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (v : ℕ) :
    List.Forall₂ List.Perm (residual (a,v)) (residual (b,v)) := by
  unfold residual
  rw [h.length_eq]
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_map_left_iff.mpr
  generalize List.range (b.length-2)=is
  induction is with
  | nil=>exact .nil
  | cons i is ih=>exact .cons (rows_getD h _) ih
lemma valid_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (e : ℕ×ℕ) :
    valid (((a,ps),ls),e)=valid (((b,ps),ls),e) := by
  simp only [valid,h.length_eq,(rows_getD h _).mem_iff]
lemma fastBranch_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (v : ℕ) :
    fastBranch (((a,ps),ls),v)=fastBranch (((b,ps),ls),v) :=
  cappedCount_rows (residual_rows h v) ps ls
lemma fastEdgeCount_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (e : ℕ×ℕ) :
    fastEdgeCount (((a,ps),ls),e)=fastEdgeCount (((b,ps),ls),e) := by
  simp only [fastEdgeCount,valid_rows h,fastBranch_rows h]
lemma fastProbabilities_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) :
    fastProbabilities ((a,ps),ls)=fastProbabilities ((b,ps),ls) := by
  simp only [fastProbabilities,fastProbability,h.length_eq,fastEdgeCount_rows h,cappedCount_rows h]
lemma fastDraw_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (bits : List Bool) :
    fastDraw (((a,ps),ls),bits)=fastDraw (((b,ps),ls),bits) := by
  simp only [fastDraw,fastProbabilities_rows h]
lemma fastSelected_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (bits : Bits) :
    fastSelected (((a,ps),ls),bits)=fastSelected (((b,ps),ls),bits) := by
  simp only [fastSelected,h.length_eq,fastDraw_rows h]
lemma clippedAssemble_cap {as bs : Bags} (h : as.length=bs.length) (ps : Parents) (ls : List ℕ) (x : Frame×Result) :
    clippedAssemble (((as,ps),ls),x)=clippedAssemble (((bs,ps),ls),x) := by
  simp only [clippedAssemble,clippedAt,capacity,h]
lemma fastRawSample_rows {as bs : Bags} (ho : List.Forall₂ List.Perm as bs)
    (ps : Parents) (ls : List ℕ) (f : ℕ) {a b : Bags} (h : List.Forall₂ List.Perm a b) (bits : Bits) :
    fastRawSample ((as,ps),ls) f ((a,ps),ls) bits=fastRawSample ((bs,ps),ls) f ((b,ps),ls) bits := by
  induction f generalizing a b with
  | zero=>rfl
  | succ f ih=>
    simp only [fastRawSample,h.length_eq,fastSelected_rows h,nextContext]
    split_ifs
    · rw [ih (residual_rows h _),clippedAssemble_cap ho.length_eq]
    · rfl
lemma fastSample_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) (bits : Bits) :
    fastSample (((a,ps),ls),bits)=fastSample (((b,ps),ls),bits) := by
  simp only [fastSample,h.length_eq,fastRawSample_rows h ps ls _ h]
lemma fastSample_represented {n m k : ℕ} (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (a : Bags) (h : List.Forall₂ List.Perm a (orderedRep bags)) (bits : Fin n → Fin k → Bool) :
    fastSample (((a,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),List.ofFn (fun i=>List.ofFn (bits i)))=
      resultRep (UnitRefresh.Materialized.sampleUnit k n bags rank parent hb hne hp hz bits) := by
  rw [fastSample_rows h,fastSample_eq bags rank parent hb hne hp hz bits]
end MatchingFPRAS.ExecutableUnit

end OAI
