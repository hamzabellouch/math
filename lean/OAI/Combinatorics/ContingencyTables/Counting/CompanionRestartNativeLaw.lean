import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartDataLaw

namespace OAI

/-! # A common native bit width for all initial plain states -/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

private lemma normalize_varying_law {X Y : Type*} [Fintype X] [DecidableEq X]
    (a l j : ℕ) (hl : l=j) (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (f : List Bool → Y) (e : X → Y) (x : X)
    (ha : a=∑ i : Fin j,width i.val)
    (h : SameLaw (fun bits : Fin a → Bool => f (List.ofFn bits))
      (fun bits : Fin (∑ i : Fin l,width i.val) → Bool =>
        e (varyingWalk width step x l (varyingWordEquiv width l bits)))) :
    SameLaw (fun bits : Fin (∑ i : Fin j,width i.val) → Bool => f (List.ofFn bits))
      (fun bits : Fin (∑ i : Fin j,width i.val) → Bool =>
        e (varyingWalk width step x j (varyingWordEquiv width j bits))) := by
  cases hl
  exact SameLaw.word_length ha f _ h

def sumBits (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) : ℕ :=
  ∑ i : Fin j,sourceWidth A C K parameters i.val

lemma widthSum_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    (∑ i : Fin (baseData A C K j parameters z v reserve w S).1.length,
      widthAt (baseData A C K j parameters z v reserve w S) i.val)=sumBits A C K j parameters := by
  have hn : (baseData A C K j parameters z v reserve w S).1.length=j := by
    simp only [baseData,stagesData,List.length_ofFn]
  rw [hn]
  exact Finset.sum_congr rfl (fun i _ => widthAt_data A C K j parameters z v reserve w S i)

theorem output_native_sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hH : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (parameters : CountingPhaseParametersProgram.Input)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin (sumBits A C K j parameters) → Bool =>
      output (baseData A C K j parameters z v reserve w S.val.val,List.ofFn bits))
      (fun bits : Fin (sumBits A C K j parameters) → Bool =>
        encodeSet (coordinateOrder A)
          (varyingWalk (sourceWidth A C K parameters) (sourceStep A C K parameters hK hW v w) S j
            (varyingWordEquiv (sourceWidth A C K parameters) j bits)).val.val) := by
  have h := output_data_sameLaw A C K j hC hH hK hW hB parameters hxi z v reserve hdegree hdepth w S
  have hn := widthSum_data A C K j parameters z v reserve w S.val.val
  have hl : (baseData A C K j parameters z v reserve w S.val.val).1.length=j := by
    simp only [baseData,stagesData,List.length_ofFn]
  exact normalize_varying_law _ _ j hl (sourceWidth A C K parameters)
    (sourceStep A C K parameters hK hW v w)
    (fun bits => output (baseData A C K j parameters z v reserve w S.val.val,bits))
    (fun T => encodeSet (coordinateOrder A) T.val.val) S hn h

end
end ContingencyTables.CompanionRestartProgram

end OAI
