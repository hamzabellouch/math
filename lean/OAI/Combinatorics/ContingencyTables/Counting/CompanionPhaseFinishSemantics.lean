import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseWords

namespace OAI

/-! # Exact semantics of the stored phase update -/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS CompanionFactorialApplication CompanionTraceProgram CompanionPhaseCounts
open CompanionMultiplierMatrixProgram CompanionMultiplierProgram CompanionOrderedProposal
open CompanionArithmeticProposal CompanionRationalUpdates CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p q N : ℕ} (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin q)

def data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (estimate : Fraction) (values : Fin N→Fraction×Fraction) : Input :=
  ((((orderedCatalog A g e,(List.ofFn states).map (encodeSet e)),matrixCode w),estimate),List.ofFn values)

lemma termInput_data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) (i : Fin N) :
    termInput (data A g e states w E values,i.val)=
      ((orderedCatalog A g e,encodeSet e (states i)),values i) := by
  simp only [termInput,data,trajectory,List.map_ofFn,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta,Function.comp_apply]

lemma term_value (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) (i : Fin N) :
    TreeFraction.val (indexedTerm (data A g e states w E values,i.val))=
      if PlainState pairs (states i) then TreeFraction.val (values i).2/TreeFraction.val (values i).1 else 0 := by
  rw [indexedTerm,termInput_data]
  have hp : pairedPlainTest (orderedCatalog A g e,encodeSet e (states i))=
      decide (PlainState pairs (states i)) :=
    Bool.eq_iff_iff.mpr (by simp only [plainTest_ordered,decide_eq_true_eq])
  unfold term
  rw [hp]
  by_cases h : PlainState pairs (states i)
  · simp only [h,decide_true,ite_true,TreeFraction.div_val]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,TreeFraction.val,
      Nat.cast_zero,Nat.cast_one,zero_div]

lemma terms_data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) :
    terms (data A g e states w E values)=
      List.ofFn (fun i : Fin N => indexedTerm (data A g e states w E values,i.val)) := by
  unfold terms indices trajectory data
  simp only [List.length_map,List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.length_map,List.length_range] at hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

lemma terms_den_pos (z : Input) (x : Fraction) (hx : x∈terms z) : 0 < x.2 := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact term_den_pos _

lemma ratio_data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) :
    TreeFraction.val (ratio (data A g e states w E values))=
      (∑ i,if PlainState pairs (states i) then TreeFraction.val (values i).2/TreeFraction.val (values i).1 else 0)/
        (plainCount A (List.ofFn states):ℚ) := by
  rw [ratio,TreeFraction.div_val,total,TreeFraction.sum_val _ (terms_den_pos _)]
  rw [terms_data]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,term_value]
  have hc : TreeFraction.val (count (data A g e states w E values))=
      (plainCount A (List.ofFn states):ℚ) := by
    unfold count trajectory data
    rw [plainCount_code]
    simp only [TreeFraction.val,Nat.cast_one,div_one]
  rw [hc]

lemma updated_entry (states : Fin N→Set (Labels A×Bool)) (hl : 0 < N)
    (w : Fin p→Fin p→Fraction) (old : CompanionPhaseWords.Stored A)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (g i)) (pair (g j))) (i j : Fin p) :
    TreeFraction.val (readEntry
      (updateMatrix ((orderedCatalog A g e,(List.ofFn states).map (encodeSet e)),matrixCode w),(i.val,j.val)))=
      rationalLearn pairs old.multiplier (List.ofFn states) (pair (g i)) (pair (g j)) := by
  rw [updateMatrix_code,readEntry_code,updateCode_value,
    plainCount_code,defectCount_code,hw]
  rw [rationalLearn_counts A old.multiplier (List.ofFn states) (by simpa only [List.length_ofFn] using hl)]
  have hp : pair (g i)∈(pairs : List (Pair A)) := pair_mem _
  have hq : pair (g j)∈(pairs : List (Pair A)) := pair_mem _
  have he : pair (g i)=pair (g j) ↔ i=j :=
    ⟨fun h => g.injective (pair_injective h),fun h => congrArg (fun k => pair (g k)) h⟩
  by_cases hij : i=j
  · subst j
    simp only [hp,ne_eq,not_true_eq_false,and_false,ite_false,ite_true]
  · have hv : i.val≠j.val := fun h => hij (Fin.ext h)
    have hpq : pair (g i)≠pair (g j) := fun h => hij (he.mp h)
    simp only [hv,hp,hq,true_and,ite_false]
    exact (ite_eq_left hpq).symm

/-- The relevant view of a physical stored value consists of its actual
label-pair entries and its rational estimate. -/
def view (z : Stored) : (Fin p→Fin p→ℚ)×ℚ :=
  ((fun i j => TreeFraction.val (readEntry (z.1,(i.val,j.val)))),TreeFraction.val z.2)

def storedView (s : CompanionPhaseWords.Stored A) : (Fin p→Fin p→ℚ)×ℚ :=
  ((fun i j => s.multiplier (pair (g i)) (pair (g j))),s.estimate)

/-- The phase result as a function of just the rational query values. -/
def rationalResult (states : Fin N→Set (Labels A×Bool)) (old : CompanionPhaseWords.Stored A)
    (values : List (ℚ×ℚ)) : Option ((Fin p→Fin p→ℚ)×ℚ) :=
  if CountsPositive A (List.ofFn states) then
    some ((fun i j => rationalLearn pairs old.multiplier (List.ofFn states) (pair (g i)) (pair (g j))),
      old.estimate*((∑ i : Fin N,if PlainState pairs (states i) then
        (values.getD i.val (0,0)).2/(values.getD i.val (0,0)).1 else 0)/
          (plainCount A (List.ofFn states):ℚ)))
  else none

lemma output_values (states : Fin N→Set (Labels A×Bool))
    (old : CompanionPhaseWords.Stored A) (w : Fin p→Fin p→Fraction) (E : Fraction)
    (values : Fin N→Fraction×Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (g i)) (pair (g j)))
    (hE : TreeFraction.val E=old.estimate) :
    (output (data A g e states w E values)).map (view (p := p))=
      rationalResult A g states old (List.ofFn (fun i =>
        (TreeFraction.val (values i).1,TreeFraction.val (values i).2))) := by
  have ht : positiveCounts (trajectory (data A g e states w E values))=true ↔
      CountsPositive A (List.ofFn states) := positiveCounts_code A g e (List.ofFn states)
  by_cases hp : CountsPositive A (List.ofFn states)
  · have hN : 0 < N := by
      simpa only [List.length_ofFn] using hp.1.trans_le (plainCount_le A (List.ofFn states))
    simp only [output,ht.mpr hp,ite_true,Option.map_some,rationalResult,hp]
    apply congrArg Option.some
    apply Prod.ext
    · funext i k
      exact updated_entry A g e states hN w old hw i k
    · change TreeFraction.val (estimate (data A g e states w E values))=_
      rw [estimate,TreeFraction.mul_val,ratio_data]
      dsimp only [data]
      rw [hE]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  · have htest : positiveCounts (trajectory (data A g e states w E values))=false :=
      Bool.eq_false_iff.mpr (fun h => hp (ht.mp h))
    simp only [output,htest,Bool.false_eq_true,ite_false,Option.map_none,rationalResult,hp]

/-- Applying the physical arithmetic and then reading its canonical entries
is exactly the source update, including the abort outcome. -/
theorem output_update (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : GridBoundary.Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (old : CompanionPhaseWords.Stored A) (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction)
    (bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (g i)) (pair (g j)))
    (hE : TreeFraction.val E=old.estimate)
    (hv : ∀ i,
      TreeFraction.val (values i).1=RootedWeightOracle.evaluate A R C K hK hW j xi v (states i)
        (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).1 ∧
      TreeFraction.val (values i).2=RootedWeightOracle.evaluate A R C K hK hW (j+1) xi v (states i)
        (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).2) :
    (output (data A g e states w E values)).map (view (p := p))=
      (RootedPhaseWords.update A R C K j N hK hW xi v old states bits).map (storedView A g) := by
  have ht : positiveCounts (trajectory (data A g e states w E values))=true ↔
      CountsPositive A (List.ofFn states) :=
    positiveCounts_code A g e (List.ofFn states)
  have hr : TreeFraction.val (ratio (data A g e states w E values))=
      RootedPhaseWords.observedRatio A R C K j N hK hW xi v states bits := by
    rw [ratio_data]
    unfold RootedPhaseWords.observedRatio
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [(hv i).1,(hv i).2]
    rfl
  by_cases hp : CountsPositive A (List.ofFn states)
  · have htest := ht.mpr hp
    have hN : 0 < N := by
      simpa only [List.length_ofFn] using hp.1.trans_le (plainCount_le A (List.ofFn states))
    simp only [output,htest,ite_true,Option.map_some,RootedPhaseWords.update,hp]
    apply congrArg Option.some
    apply Prod.ext
    · funext i k
      change TreeFraction.val (readEntry
        (updateMatrix ((orderedCatalog A g e,(List.ofFn states).map (encodeSet e)),matrixCode w),
          (i.val,k.val)))=rationalLearn pairs old.multiplier (List.ofFn states) (pair (g i)) (pair (g k))
      exact updated_entry A g e states hN w old hw i k
    · change TreeFraction.val (estimate (data A g e states w E values))=
        old.estimate*RootedPhaseWords.observedRatio A R C K j N hK hW xi v states bits
      rw [estimate,TreeFraction.mul_val,hr]
      exact congrArg (fun q => q*RootedPhaseWords.observedRatio A R C K j N hK hW xi v states bits) hE
  · have htest : positiveCounts (trajectory (data A g e states w E values))=false :=
      Bool.eq_false_iff.mpr (fun h => hp (ht.mp h))
    simp only [output,htest,Bool.false_eq_true,ite_false,Option.map_none,RootedPhaseWords.update,hp]

lemma rationalResult_phase (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : GridBoundary.Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (old : CompanionPhaseWords.Stored A) (states : Fin N→Set (Labels A×Bool))
    (bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool) :
    rationalResult A g states old (List.ofFn (fun i =>
      (RootedWeightOracle.evaluate A R C K hK hW j xi v (states i)
        (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).1,
       RootedWeightOracle.evaluate A R C K hK hW (j+1) xi v (states i)
        (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).2)))=
      (RootedPhaseWords.update A R C K j N hK hW xi v old states bits).map (storedView A g) := by
  by_cases hp : CountsPositive A (List.ofFn states)
  · simp only [rationalResult,RootedPhaseWords.update,hp,ite_true,Option.map_some,storedView]
    apply congrArg Option.some
    apply Prod.ext
    · rfl
    · change old.estimate * _ = old.estimate * _
      unfold RootedPhaseWords.observedRatio
      apply congrArg (fun t : ℚ => old.estimate*(t/(plainCount A (List.ofFn states):ℚ)))
      apply Finset.sum_congr rfl
      intro i _
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
      rfl
  · simp only [rationalResult,RootedPhaseWords.update,hp,ite_false,Option.map_none]

end
end ContingencyTables.CompanionPhaseFinishProgram

end OAI
