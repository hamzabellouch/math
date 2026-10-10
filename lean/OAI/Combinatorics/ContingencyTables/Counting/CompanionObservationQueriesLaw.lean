import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservationQueriesProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEvaluatedWeightLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseWords

namespace OAI

/-! # Exact independent laws for the executed observation queries -/
namespace ContingencyTables.CompanionObservationQueriesProgram
open MatchingFPRAS DensePrograms GridBoundary FairBits CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle
open scoped Classical
noncomputable section
attribute [local irreducible] queryWidth queryPair RootedLabelWeightProgram.output
  RootedLabelWeightProgram.config RootedEstimatorMedianProgram.context RootedEstimatorLayoutProgram.wordWidth

lemma queryPair_ofFn (cs : Config×Config) (code : List ℕ)
    (bits : Fin (blockWidth cs)→Bool) :
    queryPair (cs,(code,List.ofFn bits))=
      (RootedLabelWeightProgram.output (cs.1,(code,List.ofFn (splitWordEquiv _ _ bits).1)),
       RootedLabelWeightProgram.output (cs.2,(code,List.ofFn (splitWordEquiv _ _ bits).2))) := by
  unfold queryPair currentInput nextInput
  dsimp only
  rw [ofFn_split_take,ofFn_split_drop]
  rw [List.take_of_length_le (show (List.ofFn (splitWordEquiv (queryWidth cs.1)
    (queryWidth cs.2) bits).2).length ≤ queryWidth cs.2 by simp only [List.length_ofFn,le_refl])]

lemma output_ofFn {N : ℕ} (cs : Config×Config) (codes : Fin N→List ℕ)
    (bits : Fin (N*blockWidth cs)→Bool) :
    output (cs,(List.ofFn codes,List.ofFn bits))=
      List.ofFn (fun i => queryPair
        (cs,(codes i,List.ofFn (gridWordEquiv N (blockWidth cs) bits i)))) := by
  unfold output indices
  simp only [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi' : i < N := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,indexedPair,indexedInput,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi',dite_true,Option.getD_some]
    have hw := wordChunk_ofFn bits ⟨i,hi'⟩
    exact congrArg (fun bs => queryPair (cs,(codes ⟨i,hi'⟩,bs))) hw

def values (xs : List (Fraction×Fraction)) : List (ℚ×ℚ) :=
  xs.map (fun z => (TreeFraction.val z.1,TreeFraction.val z.2))

/-- Each trajectory position gets its own independent current and next query. -/
theorem sameLaw {N : ℕ} {U V : Type*} [Fintype U] [Fintype V]
    (cs : Config×Config) (codes : Fin N→List ℕ) (f : Fin N→U→ℚ) (g : Fin N→V→ℚ)
    (hf : ∀ i,SameLaw (fun bits : Fin (queryWidth cs.1)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output (cs.1,(codes i,List.ofFn bits)))) (f i))
    (hg : ∀ i,SameLaw (fun bits : Fin (queryWidth cs.2)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output (cs.2,(codes i,List.ofFn bits)))) (g i)) :
    SameLaw (fun bits : Fin (N*blockWidth cs)→Bool =>
      values (output (cs,(List.ofFn codes,List.ofFn bits))))
      (fun bits : Fin N→U×V => List.ofFn (fun i => (f i (bits i).1,g i (bits i).2))) := by
  have h := (FiniteObservableTransport.indexed N _ _ (fun i => (hf i).prod (hg i))).map List.ofFn
  let e : (Fin (N*blockWidth cs)→Bool) ≃
      (Fin N→(Fin (queryWidth cs.1)→Bool)×(Fin (queryWidth cs.2)→Bool)) :=
    (gridWordEquiv N (blockWidth cs)).trans (Equiv.piCongrRight (fun _ => splitWordEquiv _ _))
  intro phi
  have he := uniformAverage_equiv e (fun xs => phi (List.ofFn (fun i =>
    (TreeFraction.val (RootedLabelWeightProgram.output (cs.1,(codes i,List.ofFn (xs i).1))),
      TreeFraction.val (RootedLabelWeightProgram.output (cs.2,(codes i,List.ofFn (xs i).2)))))))
  have hout : (fun bits : Fin (N*blockWidth cs)→Bool =>
      phi (values (output (cs,(List.ofFn codes,List.ofFn bits)))))=
      (fun bits => phi (List.ofFn (fun i =>
        (TreeFraction.val (RootedLabelWeightProgram.output (cs.1,(codes i,List.ofFn (e bits i).1))),
          TreeFraction.val (RootedLabelWeightProgram.output (cs.2,(codes i,List.ofFn (e bits i).2))))))) := by
    funext bits
    rw [output_ofFn]
    simp only [values,List.map_ofFn,queryPair_ofFn]
    rfl
  rw [hout]
  exact he.trans (h phi)

variable {m n : ℕ}
lemma queryWidth_config (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) :
    queryWidth (RootedLabelWeightProgram.config A C K j xi xi z v degree depth)=
      medianEstimatorBits A C K j xi xi := by
  unfold queryWidth RootedLabelWeightProgram.config
  exact CompanionEvaluatedWeightProgram.queryWidth A C K j xi z v

lemma sameLaw_query (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (S : Set (Labels A×Bool)) :
    SameLaw (fun bits : Fin (queryWidth
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth))→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
          (encodeSet (coordinateOrder A) S,List.ofFn bits))))
      (RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T) C K hK hW j xi
        (RootedCatalogGrid.gridEquiv A K v) S) := by
  have h := RootedLabelWeightProgram.sameLaw_weight A C K j hC hj hK hW hB xi hxi z v
    degree depth hdegree hdepth S
  exact SameLaw.word_length
    ((CompanionEvaluatedWeightProgram.queryWidth A C K j xi (profile A S) v).trans
      (queryWidth_config A C K j xi z v degree depth).symm) (fun bs => TreeFraction.val (RootedLabelWeightProgram.output
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
          (encodeSet (coordinateOrder A) S,bs)))) _ h

/-- The two physical configurations used for observing one phase. -/
def phaseConfigs (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool) : Config×Config :=
  (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
    RootedLabelWeightProgram.config A C K (j+1) xi xi z v nextDegree nextDepth)

lemma blockWidth_phaseConfigs (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool) :
    blockWidth (phaseConfigs A C K j xi z v degree depth nextDegree nextDepth)=
      CompanionPhaseWords.observationBits A C K j xi := by
  unfold blockWidth phaseConfigs CompanionPhaseWords.observationBits
  rw [queryWidth_config,queryWidth_config]

/-- All state observations use the exact selected-root oracle law, independently. -/
theorem sameLaw_phase (A : Instance (Fin m) (Fin n)) (C K j N : ℕ)
    (hC : 0 < C) (hj : j+1 ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (states : Fin N→Set (Labels A×Bool)) :
    let cs := phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : Fin (N*blockWidth cs)→Bool =>
      values (output (cs,(List.ofFn (fun i => encodeSet (coordinateOrder A) (states i)),List.ofFn bits))))
      (fun bits : Fin N→WeightWord A C K j xi × WeightWord A C K (j+1) xi =>
        List.ofFn (fun i =>
          (RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T) C K hK hW j xi
            (RootedCatalogGrid.gridEquiv A K v) (states i) (bits i).1,
           RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T) C K hK hW (j+1) xi
            (RootedCatalogGrid.gridEquiv A K v) (states i) (bits i).2))) := by
  dsimp only
  exact sameLaw _ _ _ _
    (fun i => sameLaw_query A C K j hC (by omega) hK hW hB xi hxi z v degree depth hdegree hdepth (states i))
    (fun i => sameLaw_query A C K (j+1) hC hj hK hW hB xi hxi z v nextDegree nextDepth hnextDegree hnextDepth (states i))

end
end ContingencyTables.CompanionObservationQueriesProgram

end OAI
