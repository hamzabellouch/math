import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericSummaries

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
open Finset Transport Enlargement

variable {E : Type} [DecidableEq E]
def selectedMarks (s : Finset E) (m : ↥s→Fin 3) (e : E) : Fin 3 :=
  if h:e∈s then m ⟨e,h⟩ else 0
lemma selectedMarks_on (s : Finset E) (m : ↥s→Fin 3) (e : ↥s) :
    selectedMarks s m e.val=m e := dite_eq_left e.property
lemma selectedMarks_eq (s : Finset E) (m : ↥s→Fin 3) (r : E→Fin 3) :
    (∀ e∈s,selectedMarks s m e=r e) ↔ m=(fun e=>r e.val) := by
  constructor
  · intro h; funext e; exact (selectedMarks_on s m e).symm.trans (h e.val e.property)
  · intro h e he; subst m; simp only [selectedMarks,he,↓reduceDIte]

variable {V : Type} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V→V→ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V→V→ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _

lemma reweight_nonneg (w w₁ : V→V→ℚ) (hw : ∀ i j,0≤w i j)
    (hw₁ : ∀ i j,0≤w₁ i j) (K : ℕ) (e : BagEdge (RationalSource.bags w K)) :
    0≤RationalSource.bagReweight w w₁ K e := by
  classical
  by_cases h : ∃ q,RationalSource.coloredReal w K q=e
  · obtain ⟨q,rfl⟩:=h
    rw [RationalSource.bagReweight_on]
    unfold RationalSource.rawReweight
    split_ifs
    · apply div_nonneg
      · unfold BottleneckAlgorithm.edge; split_ifs <;> apply hw₁
      · unfold BottleneckAlgorithm.edge; split_ifs <;> apply hw
    · exact zero_le_one
  · rw [RationalSource.bagReweight_off w w₁ K e h]; exact zero_le_one

variable (w w₁ : V→V→ℚ) (K : ℕ) {S : ℕ}
    (x : Fin S→RationalSource.Marked w K)
lemma scalarA_source (i : Fin S) :
    scalarA (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2) i=
      RationalSource.observableA w K (x i) := by
  unfold scalarA RationalSource.observableA
  simp only [selectedMarks_eq]
lemma scalarD_source (i : Fin S) :
    scalarD (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2)
      (RationalSource.bagReweight w w₁ K) i=RationalSource.observableD w w₁ K (x i) := by
  unfold scalarD RationalSource.observableD
  simp only [selectedMarks_eq]
lemma scalarProbe_source (e : LogicalEdge V) (i : Fin S) :
    scalarProbe (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2)
      (RationalSource.bagReweight w w₁ K) (RationalSource.centralEdge w K e) i=
      RationalSource.observableProbe w w₁ K e (x i) := by
  unfold scalarProbe RationalSource.observableProbe
  simp only [selectedMarks_eq]
  simp only [singleton_subset_iff,mem_singleton]
  congr 3
  · funext a
    split_ifs <;> rfl
  · congr 1
    exact Subsingleton.elim _ _

noncomputable def sourceSamples : List (ExecutableMarking.Marks ℕ) :=
  List.ofFn (fun i=>numericMarks (x i).1.val (selectedMarks (x i).1.val (x i).2))
noncomputable def sourceKeys : List (BagEdge (RationalSource.bags w K)) :=
  List.ofFn (UnitRefresh.orderedEnum _)
lemma mem_sourceKeys (e : BagEdge (RationalSource.bags w K)) : e∈sourceKeys w K :=
  List.mem_ofFn.mpr ⟨(UnitRefresh.orderedEnum _).symm e,Equiv.apply_symm_apply _ _⟩

lemma summaries_source (hw : ∀ i j,0≤w i j) (hw₁ : ∀ i j,0≤w₁ i j) (D : ℕ) :
    summaries ((reweightsRep (RationalSource.bagReweight w w₁ K),(D,(sourceKeys w K).map index)),
      sourceSamples w K x)=
      ((TreeFraction.repr (Counting.ratioEstimate
          (FiniteTrial.sampleAverage (RationalSource.observableA w K) x)
          (FiniteTrial.sampleAverage (RationalSource.observableD w w₁ K) x)),
        TreeFraction.repr (FiniteTrial.sampleAverage (RationalSource.observableD w w₁ K) x)),
       (sourceKeys w K).map (fun e=>(index e,TreeFraction.repr
        ((∑ i,scalarProbe (fun j=>(x j).1.val) (fun j=>selectedMarks (x j).1.val (x j).2)
          (RationalSource.bagReweight w w₁ K) e i)/(S:ℚ))))) := by
  unfold sourceSamples
  rw [summaries_rep _ _ _ (reweight_nonneg w w₁ hw hw₁ K)]
  simp only [scalarA_source,scalarD_source,FiniteTrial.sampleAverage]
end MatchingFPRAS.NumericMarking

end OAI
