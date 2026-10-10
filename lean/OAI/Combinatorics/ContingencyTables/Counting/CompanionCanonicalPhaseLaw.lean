import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterPhaseLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterWidths
import OAI.Combinatorics.ContingencyTables.Counting.CompanionHistoryReadback

namespace OAI

/-! # The projected law of one complete physical counting phase -/
namespace ContingencyTables.CompanionCanonicalPhaseLaw
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionCanonicalHistory
open CompanionHistoryReadback CompanionStoredRepresentation CompanionOracleDensity
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped Classical
noncomputable section

lemma prefix_sameLaw {Z : Type*} {k N : ℕ} (hk : k ≤ N) (f : (Fin k→Bool)→Z) :
    SameLaw (fun bits : Fin N→Bool => f (prefixWord hk bits)) f := by
  intro phi
  have he := uniformAverage_equiv (paddingWordEquiv hk)
    (fun p : (Fin k→Bool)×(Fin (N-k)→Bool) => phi (f p.1))
  simp only [paddingWordEquiv_fst] at he
  rw [uniformAverage_prod] at he
  simpa only [uniformAverage_const] using he

def canonicalResult {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (j : ℕ)
    (bits : RootedRestartTrial.Words A s.C s.K s.H s.L j s.k s.n s.N s.h s.xi) :
    Canonical (p := p) :=
  let hs := history.map (extend A g)
  let old := RootedStoredHistory.lookup A hs j
  project A g ((RootedRestartTrial.run A R s.C s.K s.H s.L j s.k s.n s.N s.h
    s.hK s.hW s.xi s.v (fun i => (RootedStoredHistory.lookup A hs i).multiplier)
      old.estimate bits).getD old)

theorem canonicalStep_sameLaw {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (hj : history.length < s.H) :
    SameLaw (fun bits : RootedPhaseHistory.Word A s => canonicalStep A g R s history bits)
      (canonicalResult A g R s history history.length) := by
  let f := fun bits : Fin (RootedPhaseHistory.width A s history.length)→Bool =>
    canonicalResult A g R s history history.length (RootedPhaseHistory.split A s history.length bits)
  have hp := prefix_sameLaw (RootedPhaseHistory.width_le A s history.length hj) f
  intro phi
  have he := uniformAverage_equiv (RootedPhaseHistory.split A s history.length)
    (fun bits => phi (canonicalResult A g R s history history.length bits))
  have hf (bits : RootedPhaseHistory.Word A s) :
      canonicalStep A g R s history bits=
        f (prefixWord (RootedPhaseHistory.width_le A s history.length hj) bits) := by
    unfold canonicalStep RootedPhaseHistory.step
    rw [show (history.map (extend A g)).length=history.length from List.length_map _]
    rw [dite_eq_left hj]
    rfl
  simp_rw [hf]
  exact (hp phi).trans he

private theorem project_getD {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (a b : Option (CompanionPhaseWords.Stored A)) (s t : CompanionPhaseWords.Stored A)
    (h : a.map (project A g)=b.map (project A g)) (he : project A g s=project A g t) :
    project A g (a.getD s)=project A g (b.getD t) := by
  cases a <;> cases b <;> simp_all

variable {m n : ℕ}

def rawSettings (A : Instance (Fin m) (Fin n)) (C K H N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : RootedPhaseHistory.Settings A where
  C := C
  K := K
  H := H
  L := L
  k := CountingPhaseParametersProgram.precision (CompanionInitializedRestartProgram.parameters A H
    (CompanionTargetMixing.restartTime A H L) N R L epsilon)
  n := R
  N := CountingPhaseParametersProgram.observations (CompanionInitializedRestartProgram.parameters A H
    (CompanionTargetMixing.restartTime A H L) N R L epsilon)
  h := CountingPhaseSchedule.initialPrecision H
  hK := hK
  hW := hW
  xi := TreeFraction.val (CountingPhaseParametersProgram.noise
    (CompanionInitializedRestartProgram.parameters A H (CompanionTargetMixing.restartTime A H L) N R L epsilon))
  v := RootedCatalogGrid.gridEquiv A K v

theorem rawSettings_eq (A : Instance (Fin m) (Fin n)) (s : RootedPhaseHistory.Settings A)
    (N : ℕ) (epsilon : TreeFraction.Fraction)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.k)
    (hN : CountingPhaseParametersProgram.observations
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.N)
    (hh : CountingPhaseSchedule.initialPrecision s.H=s.h)
    (hxi : TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon))=s.xi)
    (hv : RootedCatalogGrid.gridEquiv A s.K v=s.v) :
    rawSettings A s.C s.K s.H N s.n s.L epsilon s.hK s.hW v=s := by
  cases s
  dsimp only at hk hN hh hxi hv ⊢
  unfold rawSettings
  congr 1

def sourceStored (A : Instance (Fin m) (Fin n))
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (i : ℕ) : CompanionPhaseWords.Stored A :=
  ⟨sourceWeights A (matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history i),
    TreeFraction.val (estimateAt initial history i)⟩

lemma sourceStored_project (A : Instance (Fin m) (Fin n))
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (i : ℕ) :
    project A (pairLabels A) (sourceStored A initial history i)=
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (lookup initial history i) := by
  apply Prod.ext
  · funext a b
    simp only [project,CompanionPhaseFinishProgram.storedView,sourceStored,sourceWeights,pair,
      Equiv.symm_apply_apply,matrixAt,entries,CompanionPhaseFinishProgram.view]
  · rfl

lemma sourceStored_lookup (A : Instance (Fin m) (Fin n))
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hi : CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
      initial=project A (pairLabels A) (RootedStoredEstimate.initialStored A)) (i : ℕ) :
    project A (pairLabels A) (sourceStored A initial history i)=
      project A (pairLabels A) (RootedStoredHistory.lookup A
        ((history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))).map (extend A (pairLabels A))) i) := by
  rw [sourceStored_project,view_lookup,CompanionCanonicalHistory.lookup_project]
  simp only [List.map_map,Function.comp_def,project_extend]
  rw [hi]
  rfl

def readbackResult (A : Instance (Fin m) (Fin n)) (s : RootedPhaseHistory.Settings A)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (bits : RootedRestartTrial.Words A s.C s.K s.H s.L history.length s.k s.n s.N s.h s.xi) :
    Canonical (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length) :=
  let old := sourceStored A initial history history.length
  project A (pairLabels A) ((RootedRestartTrial.run A (RootedCompletion.rowColumn A.T)
    s.C s.K s.H s.L history.length s.k s.n s.N s.h s.hK s.hW s.xi s.v
      (fun i => (sourceStored A initial history i).multiplier) old.estimate bits).getD old)

lemma readbackResult_eq (A : Instance (Fin m) (Fin n)) (s : RootedPhaseHistory.Settings A)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hi : CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
      initial=project A (pairLabels A) (RootedStoredEstimate.initialStored A))
    (bits : RootedRestartTrial.Words A s.C s.K s.H s.L history.length s.k s.n s.N s.h s.xi) :
    readbackResult A s initial history bits=
      canonicalResult A (pairLabels A) (RootedCompletion.rowColumn A.T) s
        (history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))) history.length bits := by
  let hs := (history.map (CompanionPhaseFinishProgram.view
    (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))).map (extend A (pairLabels A))
  have hp (i : ℕ) := sourceStored_lookup A initial history hi i
  have ho := restart_project_eq A (pairLabels A) (RootedCompletion.rowColumn A.T)
    s.C s.K s.H s.L history.length s.k s.n s.N s.h s.hK s.hW s.xi s.v
    (fun i => (sourceStored A initial history i).multiplier)
    (fun i => (RootedStoredHistory.lookup A hs i).multiplier)
    (sourceStored A initial history history.length).estimate
    (RootedStoredHistory.lookup A hs history.length).estimate
    (fun i _ => ((project_eq_iff A (pairLabels A) _ _).mp (hp i)).1)
    (((project_eq_iff A (pairLabels A) _ _).mp (hp history.length)).2) bits
  exact project_getD A (pairLabels A) _ _ _ _ ho (hp history.length)

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K H N R L W : ℕ)
    (epsilon : TreeFraction.Fraction) (hC : 0 < C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A H
        (CompanionTargetMixing.restartTime A H L) N R L epsilon)))
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hj : history.length < H) (hphase : history.length+1 ≤ rationalHeight A C)
    (hwidth : RootedPhaseHistory.totalWidth A (rawSettings A C K H N R L epsilon hK hW v) ≤ W)
    (hdegree : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hdepth : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length initial)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length q)
    (hi : CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
      initial=project A (pairLabels A) (RootedStoredEstimate.initialStored A)) :
    let s := rawSettings A C K H N R L epsilon hK hW v
    SameLaw (fun bits : Fin W→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (CompanionOuterPhaseProgram.output
          (((CompanionRestartInitializer.data A C K H
            (CompanionTargetMixing.restartTime A H L) N R L epsilon z v,initial),history),List.ofFn bits)))
      (fun bits : RootedPhaseHistory.Word A s => canonicalStep A (pairLabels A)
        (RootedCompletion.rowColumn A.T) s
        (history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))) bits) := by
  dsimp only
  let s := rawSettings A C K H N R L epsilon hK hW v
  let j := history.length
  let t := CompanionTargetMixing.restartTime A H L
  let reserve := List.replicate W false
  let padding := W-RootedPhaseHistory.width A s j
  let w := matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history
  let E := estimateAt initial history
  let view := CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
  have hbound : RootedPhaseHistory.width A s j ≤ W :=
    (RootedPhaseHistory.width_le A s j hj).trans hwidth
  have hsize : CompanionOuterPhaseProgram.phaseWordWidth A C K H t N R L j
      epsilon z v reserve padding=W := by
    have h := CompanionOuterWidths.phaseWidth_source A s N j epsilon z v reserve padding
      rfl rfl rfl rfl
    change CompanionOuterPhaseProgram.phaseWordWidth A C K H t N R L j
      epsilon z v reserve padding=RootedPhaseHistory.width A s j+padding at h
    exact h.trans (Nat.add_sub_of_le hbound)
  have hw (a b : LabelIndex A) : TreeFraction.val (w j a b)=
      (sourceStored A initial history j).multiplier (pair (pairLabels A a)) (pair (pairLabels A b)) := by
    simp only [sourceStored,sourceWeights,pair,Equiv.symm_apply_apply]
    rfl
  have hbase := CompanionOuterPhaseProgram.output_sameLaw A C K H t N R L j padding
    hC hphase hK hW hB epsilon hxi z v reserve
    (by simpa only [reserve,List.length_replicate] using hsize.symm)
    (fun i hi => by rw [List.length_replicate]; exact hdegree i hi)
    (fun i hi => by rw [List.length_replicate]; exact hdepth i hi)
    (sourceStored A initial history j) w E hw rfl
  have hsource : SameLaw
      (fun bits : Fin (CompanionOuterPhaseProgram.phaseWordWidth A C K H t N R L j
        epsilon z v reserve padding)→Bool => view
          (CompanionOuterPhaseProgram.output
            (CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E (List.ofFn bits))))
      (readbackResult A s initial history) := hbase
  have hp := SameLaw.word_length hsize
    (fun bs => view (CompanionOuterPhaseProgram.output
      (CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E bs)))
    (readbackResult A s initial history) hsource
  have hphysical : SameLaw
      (fun bits : Fin W→Bool => view (CompanionOuterPhaseProgram.output
        (((CompanionRestartInitializer.data A C K H t N R L epsilon z v,initial),history),List.ofFn bits)))
      (readbackResult A s initial history) := by
    intro phi
    have hd (bits : Fin W→Bool) :
        CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E (List.ofFn bits)=
          (((CompanionRestartInitializer.data A C K H t N R L epsilon z v,initial),history),List.ofFn bits) :=
      outer_data_readback A C K H t N R L epsilon z v initial history hinit hh _
    simpa only [hd] using hp phi
  have href : SameLaw (readbackResult A s initial history)
      (canonicalResult A (pairLabels A) (RootedCompletion.rowColumn A.T) s
        (history.map view) j) := by
    intro phi
    apply congrArg uniformAverage
    funext bits
    rw [readbackResult_eq A s initial history hi bits]
  have hc := canonicalStep_sameLaw A (pairLabels A) (RootedCompletion.rowColumn A.T) s
    (history.map view) (by rw [List.length_map]; exact hj)
  rw [List.length_map] at hc
  intro phi
  exact (hphysical phi).trans ((href phi).trans (hc phi).symm)

end
end ContingencyTables.CompanionCanonicalPhaseLaw

end OAI
