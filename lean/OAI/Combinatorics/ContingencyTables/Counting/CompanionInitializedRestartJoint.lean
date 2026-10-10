import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitializedRestartLaw
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordJointPadding

namespace OAI

/-! # Joint restart law with the unused trajectory and query suffix -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def jointModel (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (bits : Fin (CompanionInitialDraw.initialBits A
      (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) → Bool) :
    PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))×(Fin padding → Bool) :=
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let widths := CompanionRestartProgram.sourceWidth A C K (parameters A H T N R L epsilon)
  let blocks := splitWordEquiv (CompanionInitialDraw.initialBits A B)
    (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding) bits
  let tail := splitWordEquiv (CompanionRestartProgram.sumBits A C K j
    (parameters A H T N R L epsilon)) padding blocks.2
  (varyingWalk widths
    (CompanionRestartProgram.sourceStep A C K (parameters A H T N R L epsilon) hK hW v w)
    (CompanionInitialDraw.draw A B blocks.1) j (varyingWordEquiv widths j tail.1),tail.2)

theorem output_joint_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon : TreeFraction.Fraction)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise (parameters A H T N R L epsilon)))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding))
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) :
    SameLaw (fun bits : Fin (wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) → Bool =>
      (output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits)),
        (splitWordEquiv (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon))
          padding (splitWordEquiv
            (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)))
            (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding) bits).2).2))
      (fun bits =>
        (encodeSet (coordinateOrder A) (jointModel A C K H T N R L j padding epsilon hK hW v w bits).1.val.val,
          (jointModel A C K H T N R L j padding epsilon hK hW v w bits).2)) := by
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let p := parameters A H T N R L epsilon
  let n := CompanionRestartProgram.sumBits A C K j p
  let reserve := List.replicate (wordLength A B+(n+padding)) false
  let stageList := CompanionRestartProgram.stagesData A C K j p z v reserve w
  let init := fun bits : Fin (wordLength A B) → Bool => CompanionRestartInitializer.output
    (CompanionRestartInitializer.data A C K H T N R L epsilon z v,List.ofFn bits)
  let realInit := CompanionInitialDraw.draw A B
  let encode := fun S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) =>
    encodeSet (coordinateOrder A) S.val.val
  let run := fun code (bits : Fin (n+padding) → Bool) =>
    (CompanionRestartProgram.output ((stageList,code),List.ofFn bits),(splitWordEquiv n padding bits).2)
  let sourceRun := fun S (bits : Fin n → Bool) => encode (varyingWalk
    (CompanionRestartProgram.sourceWidth A C K p)
    (CompanionRestartProgram.sourceStep A C K p hK hW v w) S j
    (varyingWordEquiv (CompanionRestartProgram.sourceWidth A C K p) j bits))
  let realRun := fun S (bits : Fin (n+padding) → Bool) =>
    (sourceRun S (splitWordEquiv n padding bits).1,(splitWordEquiv n padding bits).2)
  have hi : SameLaw init (fun bits => encode (realInit bits)) :=
    CompanionRestartInitializer.output_sameLaw A C K H T N R L epsilon z v
  have hs : ∀ S,SameLaw (run (encode S)) (realRun S) := by
    intro S
    have hn := CompanionRestartProgram.widthSum_data A C K j p z v reserve w S.val.val
    have hh := CompanionRestartProgram.output_native_sameLaw A C K j hC hj hK hW hB p hxi z v reserve
      (fun i => by simpa only [reserve,List.length_replicate] using hdegree i)
      (fun i => by simpa only [reserve,List.length_replicate] using hdepth i) w S
    exact restart_append_joint_sameLaw (CompanionRestartProgram.baseData A C K j p z v reserve w S.val.val)
      n n hn (sourceRun S) hh padding
  have hf := flat_encoded_bind (wordLength A B) (n+padding) (CompanionInitialDraw.initialBits A B) (n+padding)
    init realInit encode run realRun hi hs
  intro phi
  have h := hf phi
  have he : (fun bits : Fin (wordLength A B+(n+padding)) → Bool =>
      (output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits)),
        (splitWordEquiv n padding (splitWordEquiv (wordLength A B) (n+padding) bits).2).2))=
      (fun bits => run (init (splitWordEquiv (wordLength A B) (n+padding) bits).1)
        (splitWordEquiv (wordLength A B) (n+padding) bits).2) := by
    funext bits
    apply Prod.ext
    · exact output_split A C K H T N R L j (n+padding) epsilon z v w estimates bits
    · rfl
  rw [he]
  exact h

theorem jointModel_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) :
    SameLaw (fun bits =>
      (encodeSet (coordinateOrder A) (jointModel A C K H T N R L j padding epsilon hK hW v w bits).1.val.val,
        (jointModel A C K H T N R L j padding epsilon hK hW v w bits).2))
      (fun bits :
        (Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)) → Bool)×
          (Fin padding → Bool) =>
        (encodeSet (coordinateOrder A) (model A C K H T N R L j epsilon hK hW v w bits.1).val.val,bits.2)) := by
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let p := parameters A H T N R L epsilon
  let widths := CompanionRestartProgram.sourceWidth A C K p
  exact nested_word_joint (CompanionInitialDraw.initialBits A B)
    (CompanionRestartProgram.sumBits A C K j p) padding
    (fun initBits stageBits => encodeSet (coordinateOrder A)
      (varyingWalk widths (CompanionRestartProgram.sourceStep A C K p hK hW v w)
        (CompanionInitialDraw.draw A B initBits) j (varyingWordEquiv widths j stageBits)).val.val)


end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
